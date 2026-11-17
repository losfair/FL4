#!/usr/bin/env bash
# Build a GCE-bootable GPT image with FL4 and the SEV/DMA regression root task.
set -euo pipefail
export PATH="$PATH:/usr/sbin"
cd "$(dirname "$0")/../.."
cargo xtask sel4test-build --smp 2
b=$PWD/build/sel4test-ws/build-debug-smp2
out=$PWD/build/sev-smoke
mkdir -p "$out"
headers=()
for prefix in "$PWD/libsel4" "$b/libsel4"; do
    for inc in include arch_include/x86 sel4_arch_include/x86_64 sel4_plat_include/pc99 mode_include/64; do
        headers+=("-I$prefix/$inc")
    done
done
gcc -nostdlib -static -ffreestanding -fno-stack-protector -fno-pie -no-pie -mno-red-zone -O2 \
    "${headers[@]}" -I"$b/libsel4/autoconf" -I"$b/libsel4/gen_config" -I"$b/kernel/gen_config" \
    -Wl,-e,_start -o "$out/rootserver" xtask/tests/sev_guest.c
cd "$out"
printf 'FL4 SEV!' > module
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
# mtools operates directly on the ESP in a sparse file, without loop devices.
rm -f disk.raw
truncate -s 1G disk.raw
sgdisk -n 1:2048:+64M -t 1:ef00 disk.raw >/dev/null
mformat -i disk.raw@@1M -T 131072 -F ::
mmd -i disk.raw@@1M ::/EFI ::/EFI/BOOT
mcopy -i disk.raw@@1M BOOTX64.EFI ::/EFI/BOOT/BOOTX64.EFI
tar --format=oldgnu -Sczf fl4-sev.tar.gz disk.raw
echo "$out/fl4-sev.tar.gz"
