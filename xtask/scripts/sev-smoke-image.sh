#!/usr/bin/env bash
# Build a GCE-bootable GPT image with FL4 and the SEV/DMA regression root task.
set -euo pipefail
export PATH="$PATH:/usr/sbin"
cd "$(dirname "$0")/../.."
mode=${1:-sev}
case "$mode" in
    sev|snp) ;;
    *) echo "usage: $0 [sev|snp]" >&2; exit 2 ;;
esac
cargo xtask sel4test-build --smp 2
b=$PWD/build/sel4test-ws/build-debug-smp2
out=$PWD/build/sev-smoke
if [[ $mode == snp ]]; then out=$PWD/build/snp-smoke; fi
mkdir -p "$out"
headers=()
test_flags=()
if [[ $mode == snp ]]; then test_flags+=(-DFL4_TEST_SNP); fi
for prefix in "$PWD/libsel4" "$b/libsel4"; do
    for inc in include arch_include/x86 sel4_arch_include/x86_64 sel4_plat_include/pc99 mode_include/64; do
        headers+=("-I$prefix/$inc")
    done
done
gcc -nostdlib -static -ffreestanding -fno-stack-protector -fno-pie -no-pie -mno-red-zone -O2 \
    "${test_flags[@]}" "${headers[@]}" -I"$b/libsel4/autoconf" -I"$b/libsel4/gen_config" -I"$b/kernel/gen_config" \
    -Wl,-e,_start -o "$out/rootserver" xtask/tests/sev_guest.c
printf 'FL4 SEV!' > "$out/module"
if [[ $mode == snp ]]; then
    cargo xtask kernel
    strip --strip-debug -o "$out/kernel.elf" build/kernel.elf
    FL4_KERNEL_ELF="$out/kernel.elf" FL4_ROOTSERVER_ELF="$out/rootserver" \
        FL4_BOOT_MODULE="$out/module" cargo build --release -p fl4-efi --target x86_64-unknown-uefi
    cp target/x86_64-unknown-uefi/release/fl4-efi.efi "$out/BOOTX64.EFI"
fi
cd "$out"
if [[ $mode == sev ]]; then
    cat > grub.cfg <<'GRUB'
serial --unit=0 --speed=115200
terminal_output serial
set timeout=0
menuentry FL4 {
    multiboot2 /boot/kernel
    module2 /boot/rootserver
    module2 /boot/module
    boot
}
GRUB
    grub-mkstandalone -O x86_64-efi --locales='' --fonts='' \
        --install-modules='multiboot2 serial terminal normal memdisk tar' \
        --modules='multiboot2 serial terminal normal' -o BOOTX64.EFI \
        boot/grub/grub.cfg=grub.cfg "boot/kernel=$b/images/kernel-x86_64-pc99" boot/rootserver=rootserver boot/module=module
fi
# mtools operates directly on the ESP in a sparse file, without loop devices.
rm -f disk.raw
truncate -s 1G disk.raw
sgdisk -n 1:2048:+64M -t 1:ef00 disk.raw >/dev/null
mformat -i disk.raw@@1M -T 131072 -F ::
mmd -i disk.raw@@1M ::/EFI ::/EFI/BOOT
mcopy -i disk.raw@@1M BOOTX64.EFI ::/EFI/BOOT/BOOTX64.EFI
tar --format=oldgnu -Sczf fl4-$mode.tar.gz disk.raw
echo "$out/fl4-$mode.tar.gz"
