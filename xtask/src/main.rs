//! FL4 developer tasks: `cargo xtask <command>`.
//!
//! Every kernel run happens inside a QEMU guest (DESIGN.md §12); nothing here
//! boots FL4 on the host.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{exit, Command, Stdio};
use std::time::{Duration, Instant};

const SEL4TEST_MANIFEST: &[(&str, &str, &str)] = &[
    ("projects/musllibc", "https://github.com/seL4/musllibc.git", "b0005f86fecbd6d0257b15363a5b013446914265"),
    ("tools/nanopb", "https://github.com/nanopb/nanopb", "cad3c18ef15a663e30e3e43e3a752b66378adec1"),
    ("projects/seL4_libs", "https://github.com/seL4/seL4_libs.git", "262a34dcb2f3285be01df9e5404d911132d567a6"),
    ("tools/seL4", "https://github.com/seL4/seL4_tools.git", "6493e0c6fab360eb81a8115a49c9ca7bc280c48a"),
    ("projects/sel4_projects_libs", "https://github.com/seL4/sel4_projects_libs", "b9137c0d905ce966a02b1c9a0c6c0e4beb48223b"),
    ("projects/sel4runtime", "https://github.com/seL4/sel4runtime.git", "86489cf6efab9f314964e79468c036e9035394c7"),
    ("projects/util_libs", "https://github.com/seL4/util_libs.git", "ef49a397b7044fc38b609a99a8c6265a97913b8e"),
];

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf()
}

fn deps() -> PathBuf {
    env::var_os("FL4_DEPS")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env::var("HOME").unwrap()).join("Projects/fl4-deps"))
}

fn run(cmd: &mut Command) {
    eprintln!("+ {:?}", cmd);
    let st = cmd.status().unwrap_or_else(|e| fail(&format!("cannot run {:?}: {e}", cmd)));
    if !st.success() {
        fail(&format!("command failed ({st}): {:?}", cmd));
    }
}

fn fail(msg: &str) -> ! {
    eprintln!("xtask: {msg}");
    exit(1)
}

struct Opts {
    release: bool,
    /// x86_64 (default) or aarch64.
    arch: String,
    setup: String,
    smp: u32,
    timeout: u64,
    seeds: u64,
    rest: Vec<String>,
}

fn parse(args: &[String]) -> Opts {
    let mut o = Opts { release: false, arch: "x86_64".into(), setup: String::new(), smp: 1, timeout: 1800, seeds: 200, rest: vec![] };
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--release" => o.release = true,
            "--setup" => {
                i += 1;
                o.setup = args[i].clone();
            }
            "--arch" => {
                i += 1;
                o.arch = args[i].clone();
                if o.arch != "x86_64" && o.arch != "aarch64" {
                    fail(&format!("unknown architecture {} (x86_64, aarch64)", o.arch));
                }
            }
            "--smp" => {
                i += 1;
                o.smp = args[i].parse().unwrap();
            }
            "--seeds" => {
                i += 1;
                o.seeds = args[i].parse().unwrap();
            }
            "--timeout" => {
                i += 1;
                o.timeout = args[i].parse().unwrap();
            }
            a => o.rest.push(a.to_string()),
        }
        i += 1;
    }
    if o.setup.is_empty() {
        // AArch64 runs under TCG unless asked otherwise (the test machine
        // is x86_64, DESIGN.md section 12).
        o.setup = if o.arch == "aarch64" { "tcg".into() } else { "kvm".into() };
    }
    o
}

fn aarch64(o: &Opts) -> bool {
    o.arch == "aarch64"
}

/// The AArch64 UEFI firmware (edk2 for QEMU's virt machine).
fn aarch64_firmware() -> PathBuf {
    if let Some(p) = env::var_os("FL4_AARCH64_FIRMWARE") {
        return PathBuf::from(p);
    }
    for p in ["/usr/share/qemu-efi-aarch64/QEMU_EFI.fd", "/usr/share/AAVMF/AAVMF_CODE.fd", "/opt/homebrew/share/qemu/edk2-aarch64-code.fd", "/usr/share/edk2/aarch64/QEMU_EFI.fd"] {
        if Path::new(p).exists() {
            return PathBuf::from(p);
        }
    }
    fail("no AArch64 UEFI firmware found (set FL4_AARCH64_FIRMWARE)")
}

/// QEMU for an AArch64 image: the virt machine with UEFI firmware, booting
/// `esp` (a directory with EFI/BOOT/BOOTAA64.EFI). The setups cover the
/// device tree and ACPI, GICv2 and GICv3, and entry at EL1 and EL2.
fn qemu_cmd_aarch64(setup: &str, smp: u32, esp: &Path) -> Command {
    let mut c = Command::new("qemu-system-aarch64");
    let (accel, cpu, machine) = match setup {
        "tcg" => ("tcg", "max", "virt,acpi=off"),
        "tcg-gicv3" => ("tcg", "max", "virt,acpi=off,gic-version=3"),
        "tcg-el2" => ("tcg", "max", "virt,acpi=off,gic-version=3,virtualization=on"),
        "tcg-a57" => ("tcg", "cortex-a57", "virt,acpi=off"),
        "tcg-acpi" => ("tcg", "max", "virt,acpi=on,gic-version=3"),
        "kvm" => ("kvm", "host", "virt,acpi=off,gic-version=host"),
        "hvf" => ("hvf", "host", "virt,acpi=off"),
        s => fail(&format!("unknown AArch64 setup {s} (tcg, tcg-gicv3, tcg-el2, tcg-a57, tcg-acpi, kvm, hvf)")),
    };
    c.args(["-accel", accel, "-machine", machine, "-cpu", cpu, "-m", "2G", "-smp"]).arg(smp.to_string());
    c.args(["-display", "none", "-serial", "stdio", "-no-reboot", "-monitor", "none", "-net", "none", "-bios"]).arg(aarch64_firmware());
    c.arg("-drive").arg(format!("format=raw,file=fat:rw:{}", esp.display()));
    if let Ok(extra) = env::var("FL4_QEMU_ARGS") {
        c.args(extra.split_whitespace());
    }
    c
}

/// An EFI system partition directory that boots `image` (fl4-efi with the
/// root task built in).
fn aarch64_esp(image: &Path, dir: &Path) -> PathBuf {
    let esp = dir.join("esp");
    let _ = fs::remove_dir_all(&esp);
    fs::create_dir_all(esp.join("EFI/BOOT")).unwrap();
    fs::copy(image, esp.join("EFI/BOOT/BOOTAA64.EFI")).unwrap();
    esp
}

/// Build the AArch64 kernel and fl4-efi with `root` built in; returns the
/// UEFI image.
fn build_aarch64_image(o: &Opts, root_elf: &Path) -> PathBuf {
    let r = root();
    let mut c = Command::new("cargo");
    c.current_dir(&r).args(["build", "--release", "-p", "fl4-kernel-aarch64", "--target", "aarch64-unknown-none-softfloat"]);
    if o.release {
        c.arg("--features=release-profile");
    }
    run(&mut c);
    let out = r.join("build/aarch64");
    fs::create_dir_all(&out).unwrap();
    let elf = out.join("kernel.elf");
    // The toolchain's own lld, so no cross linker is needed.
    let sysroot = Command::new("rustc").args(["--print", "sysroot"]).output().map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string()).unwrap_or_default();
    let lld = fs::read_dir(Path::new(&sysroot).join("lib/rustlib")).ok()
        .and_then(|d| d.flatten().map(|e| e.path().join("bin/rust-lld")).find(|p| p.exists()))
        .unwrap_or_else(|| fail("rust-lld not found"));
    run(Command::new(lld).args(["-flavor", "gnu", "-n", "-static", "--gc-sections", "--build-id=none", "--strip-debug", "-u", "fl4_boot", "-T"])
        .arg(r.join("crates/fl4-kernel-aarch64/linker.ld")).arg("--whole-archive")
        .arg(r.join("target/aarch64-unknown-none-softfloat/release/libfl4_kernel_aarch64.a")).arg("-o").arg(&elf));
    run(Command::new("cargo").current_dir(&r).env("FL4_KERNEL_ELF", &elf).env("FL4_ROOTSERVER_ELF", root_elf)
        .args(["build", "--release", "-p", "fl4-efi", "--target", "aarch64-unknown-uefi"]));
    r.join("target/aarch64-unknown-uefi/release/fl4-efi.efi")
}

/// Build the standalone kernel image (default configuration).
fn build_kernel(o: &Opts) -> PathBuf {
    let r = root();
    let mut c = Command::new("cargo");
    c.current_dir(&r).args(["build", "--release", "-p", "fl4-kernel", "--target", "x86_64-unknown-none"]);
    if o.release {
        c.arg("--features=release-profile");
    }
    run(&mut c);
    let out = r.join("build");
    fs::create_dir_all(&out).unwrap();
    let elf = out.join("kernel.elf");
    run(Command::new("ld").args(["-n", "-static", "--gc-sections", "--build-id=none", "-u", "fl4_boot", "-T"]).arg(r.join("crates/fl4-kernel/linker.ld")).arg("--whole-archive").arg(r.join("target/x86_64-unknown-none/release/libfl4_kernel.a")).arg("-o").arg(&elf));
    let elf32 = out.join("kernel32.elf");
    run(Command::new("objcopy").args(["-O", "elf32-i386"]).arg(&elf).arg(&elf32));
    elf32
}

fn qemu_cmd(setup: &str, smp: u32, kernel: &Path, initrd: Option<&Path>) -> Command {
    let mut c = Command::new("qemu-system-x86_64");
    if let Ok(reject) = env::var("FL4_TEST_AP_REJECT") {
        if env::var("FL4_TEST_VERW_FIXTURE").as_deref() != Ok("1")
            || !matches!(reject.as_str(), "ibpb" | "lfence" | "smt") {
            fail("FL4_TEST_AP_REJECT requires FL4_TEST_VERW_FIXTURE=1 and ibpb, lfence, or smt");
        }
    }
    match setup {
        // The IOAPIC runs in QEMU (split irqchip): with KVM's in-kernel
        // IOAPIC, QEMU gives GSI 2 no route, so an HPET timer routed to pin
        // 2 (where sel4test's driver puts it) never interrupts.
        "kvm" => c.args(["-enable-kvm", "-machine", "kernel-irqchip=split", "-cpu", "host,+invtsc"]),
        "kvm-no-vm" => c.args(["-enable-kvm", "-machine", "kernel-irqchip=split", "-cpu", "host,-vmx,-svm"]),
        "kvm-no-ibrs" => c.args(["-enable-kvm", "-machine", "kernel-irqchip=split", "-cpu", "host,-auto-ibrs,-ibrs-all"]),
        "kvm-no-ibpb" => c.args(["-enable-kvm", "-machine", "kernel-irqchip=split", "-cpu", "host,-ibpb,-spec-ctrl"]),
        "kvm-no-rdcl" => c.args(["-enable-kvm", "-machine", "kernel-irqchip=split", "-cpu", "host,vendor=GenuineIntel,-rdctl-no"]),
        "kvm-no-pmu" => c.args(["-enable-kvm", "-machine", "kernel-irqchip=split", "-cpu", "host,pmu=off"]),
        // The fallback paths: xAPIC, the APIC one-shot timer, no PCIDs,
        // the FS/GS MSRs, XSAVEOPT.
        "kvm-reduced" => c.args(["-enable-kvm", "-machine", "kernel-irqchip=split", "-cpu", "host,-x2apic,-tsc-deadline,-pcid,-invpcid,-fsgsbase,-xsaves,-xsavec"]),
        // -icount stops QEMU 10.0 with "Bad icount read" during boot.
        "tcg" => c.args(["-accel", "tcg", "-cpu", "max"]),
        // An Intel CPU without IA32_ARCH_CAPABILITIES counts as vulnerable
        // to Meltdown: the skim window paths (TCG has no PCIDs).
        "tcg-intel" => c.args(["-accel", "tcg", "-cpu", "Skylake-Client-v1,-hle,-rtm"]),
        s => fail(&format!("unknown setup {s} (kvm, kvm-reduced, kvm-no-vm, kvm-no-ibrs, kvm-no-ibpb, kvm-no-rdcl, kvm-no-pmu, tcg, tcg-intel)")),
    };
    c.args(["-m", "3G", "-smp"]).arg(smp.to_string());
    c.args(["-display", "none", "-serial", "stdio", "-no-reboot", "-monitor", "none"]);
    // FL4_PIN=c0,c1,...: pin vCPU i to host CPU ci (run_qemu asks QEMU
    // for its vCPU threads over QMP), for performance measurements.
    if env::var_os("FL4_PIN").is_some() {
        c.arg("-qmp").arg(format!("unix:{},server=on,wait=off", qmp_socket().display()));
    }
    // Extra arguments for debugging, e.g. FL4_QEMU_ARGS=-s for gdb.
    if let Ok(extra) = env::var("FL4_QEMU_ARGS") {
        c.args(extra.split_whitespace());
    }
    c.arg("-kernel").arg(kernel);
    if let Some(i) = initrd {
        c.arg("-initrd").arg(i);
    }
    c
}

fn qmp_socket() -> PathBuf {
    root().join("build/qmp.sock")
}

/// Pin each vCPU thread of the QEMU just started to the host CPUs listed
/// in FL4_PIN (DESIGN.md §12: performance numbers come from pinned vCPUs).
fn pin_vcpus() {
    use std::io::{BufRead, BufReader, Write};
    let cpus: Vec<String> = env::var("FL4_PIN").unwrap().split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
    let path = qmp_socket();
    let start = Instant::now();
    let sock = loop {
        if let Ok(s) = std::os::unix::net::UnixStream::connect(&path) {
            break s;
        }
        if start.elapsed() > Duration::from_secs(20) {
            eprintln!("xtask: FL4_PIN: no QMP socket");
            return;
        }
        std::thread::sleep(Duration::from_millis(50));
    };
    let mut w = sock.try_clone().unwrap();
    let mut r = BufReader::new(sock);
    let mut line = String::new();
    let mut read = |r: &mut BufReader<std::os::unix::net::UnixStream>| {
        line.clear();
        r.read_line(&mut line).ok();
        line.clone()
    };
    read(&mut r);
    writeln!(w, r#"{{"execute":"qmp_capabilities"}}"#).ok();
    read(&mut r);
    writeln!(w, r#"{{"execute":"query-cpus-fast"}}"#).ok();
    let reply = read(&mut r);
    let mut tids: Vec<String> = Vec::new();
    for s in reply.split("\"thread-id\":").skip(1) {
        let tid: String = s.trim_start().chars().take_while(|c| c.is_ascii_digit()).collect();
        // Each CPU's "props" also has a "thread-id": its SMT thread number,
        // 0 here. Host thread IDs are never 0.
        if !tid.is_empty() && tid != "0" && !tids.contains(&tid) {
            tids.push(tid);
        }
    }
    for (i, tid) in tids.iter().enumerate() {
        let cpu = cpus.get(i).cloned().unwrap_or_else(|| cpus[i % cpus.len()].clone());
        let _ = Command::new("taskset").args(["-pc", &cpu, tid]).stdout(Stdio::null()).status();
    }
    eprintln!("xtask: pinned {} vCPU threads to host CPUs {}", tids.len(), cpus.join(","));
}

/// Own the test library until QEMU has exited, including timeout/error paths.
struct QemuTestFixture(PathBuf);

impl Drop for QemuTestFixture {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn qemu_test_fixture(c: &mut Command) -> std::io::Result<Option<QemuTestFixture>> {
    if env::var("FL4_TEST_VERW_FIXTURE").as_deref() != Ok("1") {
        return Ok(None);
    }
    // Concurrent test commands must not overwrite a running QEMU's library.
    let lib = root().join(format!("build/kvm-verw-fixture-{}.so", std::process::id()));
    fs::create_dir_all(lib.parent().unwrap())?;
    let fixture = QemuTestFixture(lib);
    let mut cc = Command::new("cc");
    cc.args(["-shared", "-fPIC", "-Wall", "-Wextra", "-Werror"])
        .arg(root().join("xtask/tests/kvm_verw_fixture.c")).arg("-ldl").arg("-o").arg(&fixture.0);
    eprintln!("+ {:?}", cc);
    let status = cc.status()?;
    if !status.success() {
        return Err(std::io::Error::other(format!("fixture compiler failed ({status})")));
    }
    eprintln!("xtask: TEST ONLY VERW_CLEAR fixture; no hardware buffer-clearing security claim");
    c.env("LD_PRELOAD", &fixture.0);
    Ok(Some(fixture))
}

/// Run QEMU, echo serial output, stop at `stop` or after `timeout`.
/// Returns the captured output.
fn run_qemu(mut c: Command, timeout: u64, stop: &[&str], log: &Path) -> String {
    use std::io::Read;
    let mut f = fs::File::create(log).unwrap();
    let fixture = qemu_test_fixture(&mut c).unwrap_or_else(|e| fail(&format!("cannot build QEMU test fixture: {e}")));
    eprintln!("+ {:?}", c);
    let _ = fs::remove_file(qmp_socket());
    let mut child = match c.stdout(Stdio::piped()).stdin(Stdio::null()).spawn() {
        Ok(child) => child,
        Err(e) => {
            drop(fixture);
            fail(&format!("cannot run {:?}: {e}", c));
        }
    };
    if env::var_os("FL4_PIN").is_some() {
        std::thread::spawn(pin_vcpus);
    }
    let mut out = child.stdout.take().unwrap();
    let (tx, rx) = std::sync::mpsc::channel::<Vec<u8>>();
    std::thread::spawn(move || {
        let mut buf = [0u8; 4096];
        loop {
            match out.read(&mut buf) {
                Ok(0) | Err(_) => break,
                Ok(n) => {
                    if tx.send(buf[..n].to_vec()).is_err() {
                        break;
                    }
                }
            }
        }
    });
    let start = Instant::now();
    let mut all = Vec::new();
    'outer: loop {
        match rx.recv_timeout(Duration::from_millis(200)) {
            Ok(b) => {
                use std::io::Write;
                std::io::stdout().write_all(&b).ok();
                f.write_all(&b).ok();
                all.extend_from_slice(&b);
                let s = String::from_utf8_lossy(&all);
                if stop.iter().any(|p| s.contains(p)) {
                    // Keep what follows the stop marker (a panic message).
                    while let Ok(b) = rx.recv_timeout(Duration::from_millis(300)) {
                        std::io::stdout().write_all(&b).ok();
                        f.write_all(&b).ok();
                        all.extend_from_slice(&b);
                    }
                    break 'outer;
                }
            }
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {}
            Err(_) => break,
        }
        if start.elapsed().as_secs() > timeout {
            eprintln!("\nxtask: timeout after {timeout}s");
            break;
        }
        if let Ok(Some(_)) = child.try_wait() {
            while let Ok(b) = rx.recv_timeout(Duration::from_millis(100)) {
                all.extend_from_slice(&b);
            }
            break;
        }
    }
    child.kill().ok();
    child.wait().ok();
    drop(fixture);
    String::from_utf8_lossy(&all).into_owned()
}

fn clone_at(ws: &Path, path: &str, url: &str, rev: &str) {
    let dst = ws.join(path);
    if dst.exists() {
        return;
    }
    let gd = ws.join(".gitdirs").join(path.replace('/', "_"));
    // Prefer a local mirror in FL4_DEPS/ws to save the download.
    let local = deps().join("ws").join(path);
    let src = if local.join(".git").exists() { local.to_string_lossy().into_owned() } else { url.to_string() };
    // Separate git dirs: musllibc's build expects `.git` to be a file.
    run(Command::new("git").args(["clone", "-q", "--separate-git-dir"]).arg(&gd).arg(&src).arg(&dst));
    run(Command::new("git").arg("-C").arg(&dst).args(["checkout", "-q", rev]));
}

/// sel4bench's own projects, on top of the sel4test manifest (the same
/// library revisions, from seL4/sel4bench-manifest).
const SEL4BENCH_MANIFEST: &[(&str, &str, &str)] = &[
    ("projects/projects_libs", "https://github.com/seL4/projects_libs.git", "d2511a75ffadc5550c7f303a7641c0f731c30320"),
    ("projects/sel4bench", "https://github.com/seL4/sel4bench.git", "18f9d5f079bc23551eccbdc2202cae95c72c69d7"),
];

/// A sel4bench workspace whose kernel is FL4 (`cmake/`) or upstream seL4
/// (`vendor/seL4`, the revision sel4bench pins), for the comparison of
/// DESIGN.md §12.
fn sel4bench_ws(kernel: &str) -> PathBuf {
    let r = root();
    let ws = r.join(format!("build/sel4bench-{kernel}-ws"));
    fs::create_dir_all(ws.join(".gitdirs")).unwrap();
    fs::create_dir_all(ws.join("projects")).unwrap();
    fs::create_dir_all(ws.join("tools")).unwrap();
    for (path, url, rev) in SEL4TEST_MANIFEST.iter().chain(SEL4BENCH_MANIFEST) {
        clone_at(&ws, path, url, rev);
    }
    let link = |src: &Path, dst: &Path| {
        let _ = fs::remove_file(dst);
        std::os::unix::fs::symlink(src, dst).unwrap();
    };
    let k = match kernel {
        "fl4" => r.join("cmake"),
        "sel4" => r.join("vendor/seL4"),
        k => fail(&format!("unknown kernel {k} (fl4, sel4)")),
    };
    link(&k, &ws.join("kernel"));
    link(Path::new("tools/seL4/cmake-tool/init-build.sh"), &ws.join("init-build.sh"));
    link(Path::new("projects/sel4bench/easy-settings.cmake"), &ws.join("easy-settings.cmake"));
    // sel4bench's manifest has nanopb at the top of the workspace.
    link(Path::new("tools/nanopb"), &ws.join("nanopb"));
    ws
}

/// Build and run sel4bench's IPC benchmarks on FL4 or seL4
/// (`--kernel`), both without a fastpath, release builds, one core.
fn bench(o: &Opts) {
    let kernel = o.rest.first().map(String::as_str).unwrap_or("fl4");
    let ws = sel4bench_ws(kernel);
    let b = ws.join("build");
    if !b.join("build.ninja").exists() {
        fs::create_dir_all(&b).unwrap();
        let mut c = Command::new("../init-build.sh");
        c.current_dir(&b).args([
            "-DPLATFORM=x86_64",
            "-DMCS=ON",
            "-DFASTPATH=OFF",
            "-DRELEASE=ON",
            "-DSIMULATION=OFF",
            "-DSMP=OFF",
            "-DIPC=ON",
            "-DSIGNAL=OFF",
            "-DHARDWARE=OFF",
            "-DFAULT=OFF",
            "-DSCHED=OFF",
            "-DSYNC=OFF",
            "-DMAPPING=OFF",
            "-DIRQUSER=OFF",
            "-DVCPU=OFF",
        ]);
        if kernel == "sel4" {
            // seL4 refuses to boot without PCIDs unless built without them;
            // the development machine's CPU has none (FL4 detects that).
            // The skim window is off as FL4 has it on this CPU, so both
            // kernels run the same mitigations (DESIGN.md §12).
            c.args(["-DKernelSupportPCID=OFF", "-DKernelSkimWindow=OFF"]);
        }
        python_env(&mut c);
        run(&mut c);
    }
    let mut c = Command::new("ninja");
    c.current_dir(&b);
    python_env(&mut c);
    run(&mut c);
    let k = b.join("images/kernel-x86_64-pc99");
    let i = b.join("images/sel4benchapp-image-x86_64-pc99");
    let log = b.join("sel4bench.log");
    // One vCPU pinned to one host core: performance numbers come from KVM
    // with pinned vCPUs (DESIGN.md §12).
    let mut q = Command::new("taskset");
    q.args(["-c", "2"]).arg("qemu-system-x86_64");
    let base = qemu_cmd(&o.setup, 1, &k, Some(&i));
    q.args(base.get_args());
    run_qemu(q, o.timeout, &["All is well in the universe", "FL4 panic"], &log);
    eprintln!("xtask: sel4bench results in {}", log.display());
}

/// Kernel-intensive SMP throughput of FL4 against seL4 (fl4test
/// FL4PERF0003, DESIGN.md §12): release builds of both kernels (seL4 with
/// the skim window off, as FL4 has it on this CPU), `--smp N` vCPUs (6 by
/// default) pinned to host CPUs 2.. (or FL4_PIN), three alternating rounds;
/// prints the median of each measurement. Each run takes seconds: every
/// measurement is a fixed window of TSC ticks.
fn kbench(o: &Opts) {
    let smp = if o.smp > 1 { o.smp } else { 6 };
    if env::var_os("FL4_PIN").is_none() {
        let cpus: Vec<String> = (0..smp).map(|i| (i + 2).to_string()).collect();
        env::set_var("FL4_PIN", cpus.join(","));
    }
    env::set_var("FL4_TESTS", "^FL4PERF0003$");
    let mut results: std::collections::BTreeMap<(String, String, u32), Vec<u64>> = Default::default();
    for round in 1..=3 {
        for kernel in ["fl4", "sel4"] {
            if kernel == "sel4" {
                env::set_var("FL4_KERNEL", "sel4");
            } else {
                env::remove_var("FL4_KERNEL");
            }
            let mut rest = vec!["-DReleasePrinting=ON".to_string()];
            if kernel == "sel4" {
                rest.extend(["-DKernelPrinting=ON".to_string(), "-DKernelSkimWindow=OFF".to_string()]);
            }
            let ko = Opts { release: true, arch: o.arch.clone(), setup: o.setup.clone(), smp, timeout: 120, seeds: 0, rest };
            let b = sel4test_build(&ko, false);
            let log = b.join("kbench.log");
            let out = run_qemu(
                qemu_cmd(&ko.setup, smp, &b.join("images/kernel-x86_64-pc99"), Some(&b.join("images/sel4test-driver-image-x86_64-pc99"))),
                ko.timeout,
                &["All is well in the universe", "Test suite failed", "FL4 panic"],
                &log,
            );
            let mut n = 0;
            for l in out.lines() {
                let f: Vec<&str> = l.split_whitespace().collect();
                if f.len() == 4 && f[0] == "KBENCH" {
                    let cores = f[2].trim_start_matches("cores=").parse().unwrap_or(0);
                    let v = f[3].trim_start_matches("ops_per_Mtick=").parse().unwrap_or(0);
                    results.entry((f[1].to_string(), kernel.to_string(), cores)).or_default().push(v);
                    n += 1;
                }
            }
            if !out.contains("All is well in the universe") {
                fail(&format!("kbench: {kernel} round {round} did not finish ({n} measurements; log {})", log.display()));
            }
        }
    }
    env::remove_var("FL4_KERNEL");
    let median = |v: &Vec<u64>| {
        let mut v = v.clone();
        v.sort();
        v[v.len() / 2]
    };
    println!("\nkbench: operations per million TSC ticks, all cores together (median of 3)");
    println!("{:<8} {:>5} {:>8} {:>8} {:>9}", "workload", "cores", "FL4", "seL4", "FL4/seL4");
    let order = ["yield", "signal", "ipc", "xipc", "cap", "retype", "map"];
    for w in order {
        let mut cores: Vec<u32> = results.keys().filter(|(x, k, _)| x == w && k == "fl4").map(|(_, _, c)| *c).collect();
        cores.sort();
        for c in cores {
            let (Some(a), Some(b)) = (results.get(&(w.into(), "fl4".into(), c)), results.get(&(w.into(), "sel4".into(), c))) else { continue };
            let (a, b) = (median(a), median(b));
            let r = if b == 0 { "-".to_string() } else { format!("{:.2}x", a as f64 / b as f64) };
            println!("{w:<8} {c:>5} {a:>8} {b:>8} {r:>9}");
        }
    }
}

/// FL4_KERNEL=sel4 runs sel4test on upstream seL4 (vendor/seL4) instead of
/// FL4, in its own workspace: the baseline for flaky or timing-sensitive
/// tests and for differential runs.
fn upstream() -> bool {
    env::var("FL4_KERNEL").is_ok_and(|k| k == "sel4")
}

/// The sel4test workspace: the pinned seL4 projects, sel4test itself and
/// FL4's cmake/ as the kernel (or seL4 with FL4_KERNEL=sel4).
fn sel4test_ws() -> PathBuf {
    let r = root();
    let ws = r.join(if upstream() { "build/sel4test-sel4-ws" } else { "build/sel4test-ws" });
    let gitdirs = ws.join(".gitdirs");
    fs::create_dir_all(&gitdirs).unwrap();
    fs::create_dir_all(ws.join("projects")).unwrap();
    fs::create_dir_all(ws.join("tools")).unwrap();
    for (path, url, rev) in SEL4TEST_MANIFEST {
        clone_at(&ws, path, url, rev);
    }
    let sel4test = env::var_os("SEL4TEST").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(env::var("HOME").unwrap()).join("Projects/sel4test"));
    let t = ws.join("projects/sel4test");
    if !t.exists() {
        run(Command::new("git").args(["clone", "-q", "--separate-git-dir"]).arg(gitdirs.join("sel4test")).arg(&sel4test).arg(&t));
    }
    let link = |src: &Path, dst: &Path| {
        let _ = fs::remove_file(dst);
        std::os::unix::fs::symlink(src, dst).unwrap();
    };
    // Release benchmarks print from user space (FL4PERF*), which needs
    // seL4_DebugPutChar: the seL4 tools force KernelPrinting off in every
    // release build, so -DReleasePrinting=ON (both kernels) keeps it.
    let settings = ws.join("tools/seL4/cmake-tool/helpers/application_settings.cmake");
    let text = fs::read_to_string(&settings).unwrap();
    let off = "    set(KernelPrinting OFF CACHE BOOL \"\" FORCE)\n";
    if !text.contains("ReleasePrinting") && text.contains(off) {
        let keep = format!("    if(NOT ReleasePrinting)\n  {off}    endif()\n");
        fs::write(&settings, text.replacen(off, &keep, 1)).unwrap();
    }
    // AArch64: the root server image is FL4's UEFI loader with the kernel
    // and the root task built in, not an elfloader image (cmake/
    // CMakeLists.txt defines fl4_declare_rootserver).
    let rs = ws.join("tools/seL4/cmake-tool/helpers/rootserver.cmake");
    let text = fs::read_to_string(&rs).unwrap();
    let arm = "  elseif(KernelArchARM OR KernelArchRiscV)\n";
    if !text.contains("fl4_declare_rootserver") && text.contains(arm) {
        let hook = format!("  elseif(KernelArchARM AND COMMAND fl4_declare_rootserver)\n    fl4_declare_rootserver(${{rootservername}})\n{arm}");
        fs::write(&rs, text.replacen(arm, &hook, 1)).unwrap();
    }
    link(&r.join(if upstream() { "vendor/seL4" } else { "cmake" }), &ws.join("kernel"));
    link(Path::new("tools/seL4/cmake-tool/init-build.sh"), &ws.join("init-build.sh"));
    link(Path::new("projects/sel4test/easy-settings.cmake"), &ws.join("easy-settings.cmake"));
    ws
}

fn python_env(c: &mut Command) {
    let venv = deps().join("venv/bin");
    if venv.exists() {
        let path = format!("{}:{}", venv.display(), env::var("PATH").unwrap());
        c.env("PATH", path);
    }
}

/// fl4test's tests (DESIGN.md §12) are compiled into sel4test's test
/// application; their names start with FL4. A sel4test run leaves them out
/// and an fl4test run runs only them.
const FL4TEST_REGEX: &str = "^FL4";
const SEL4TEST_REGEX: &str = "^([^F]|F[^L]|FL[^4])";

fn sel4test_build(o: &Opts, fl4test: bool) -> PathBuf {
    let ws = sel4test_ws();
    let link = ws.join("projects/sel4test/apps/sel4test-tests/src/tests/fl4test.c");
    // (fl4test needs FL4's libsel4, so upstream seL4 builds go without it.)
    if fs::symlink_metadata(&link).is_err() && !upstream() {
        std::os::unix::fs::symlink(root().join("fl4test/fl4test.c"), &link).unwrap();
    }
    // perf.c, fuzz.c and upstream.c use only the seL4 API: both kernels
    // build them.
    let extra = [("perf.c", "fl4perf.c"), ("fuzz.c", "fl4fuzz.c"), ("upstream.c", "fl4upstream.c"), ("virtualization.c", "fl4virtualization.c")];
    for (src, dst) in extra {
        let l = ws.join("projects/sel4test/apps/sel4test-tests/src/tests").join(dst);
        if fs::symlink_metadata(&l).is_err() {
            std::os::unix::fs::symlink(root().join("fl4test").join(src), &l).unwrap();
        }
    }
    // FL4_TESTS=<regex> runs only the matching tests, in its own build.
    let only = env::var("FL4_TESTS").ok().or(if fl4test { Some(FL4TEST_REGEX.into()) } else { None });
    let mut name = format!("build-{}{}-smp{}", if aarch64(o) { "aarch64-" } else { "" }, if o.release { "release" } else { "debug" }, o.smp);
    if let Some(r) = &only {
        name += "-";
        name.extend(r.chars().filter(|c| c.is_ascii_alphanumeric()));
    }
    // FL4_SERIAL_GATE=1: the test-only build where every entry takes the
    // serial gate.
    let serial_gate = env::var_os("FL4_SERIAL_GATE").is_some();
    if serial_gate {
        name += "-serialgate";
    }
    let b = ws.join(&name);
    if !b.join("build.ninja").exists() {
        fs::create_dir_all(&b).unwrap();
        let mut c = Command::new("../init-build.sh");
        if aarch64(o) {
            // QEMU's virt machine is FL4's AArch64 platform name. sel4test
            // runs it as a simulation target: without a platform timer
            // unless FL4_ARM_TIMER=1 exports the physical timer to user
            // space for its generic timer driver.
            c.current_dir(&b).args(["-DPLATFORM=qemu-arm-virt", "-DAARCH64=TRUE", "-DMCS=ON", "-DCROSS_COMPILER_PREFIX=aarch64-linux-gnu-"]);
            if env::var("FL4_ARM_TIMER").as_deref() == Ok("1") {
                c.args(["-DSel4testAllowSettingsOverride=ON", "-DSIMULATION=OFF", "-DKernelArmExportPCNTUser=ON", "-DKernelArmExportPTMRUser=ON",
                    "-DKernelIsMCS=ON", "-DKernelArmTLSReg=tpidru", "-DLibPlatSupportHaveTimer=ON"]);
            }
        } else {
            c.current_dir(&b).args(["-DPLATFORM=x86_64", "-DMCS=ON", "-DSIMULATION=OFF"]);
        }
        c.arg(format!("-DRELEASE={}", if o.release { "ON" } else { "OFF" }));
        c.arg(format!("-DSMP={}", if o.smp > 1 { "ON" } else { "OFF" }));
        if o.smp > 1 {
            c.arg(format!("-DNUM_NODES={}", o.smp));
        }
        c.arg(format!("-DLibSel4TestPrinterRegex={}", only.clone().unwrap_or_else(|| SEL4TEST_REGEX.into())));
        if serial_gate {
            c.arg("-DFL4_SERIAL_GATE=ON");
        }
        if upstream() {
            // seL4 refuses to boot without PCIDs or FSGSBASE unless built
            // without them; kvm-reduced has neither.
            c.args(["-DKernelSupportPCID=OFF", "-DKernelFSGSBase=msr"]);
        }
        for a in &o.rest {
            c.arg(a);
        }
        python_env(&mut c);
        run(&mut c);
    }
    // A build configured with another test filter (or before fl4test
    // existed) gets the one this run wants; a new test file needs CMake
    // to glob the sources again.
    let regex = only.clone().unwrap_or_else(|| SEL4TEST_REGEX.into());
    let cache = fs::read_to_string(b.join("CMakeCache.txt")).unwrap_or_default();
    let ninja = fs::read_to_string(b.join("build.ninja")).unwrap_or_default();
    let unglobbed = extra.iter().any(|(_, dst)| !ninja.contains(dst));
    if unglobbed || !cache.contains(&format!("LibSel4TestPrinterRegex:STRING={regex}\n")) {
        let mut c = Command::new("cmake");
        c.current_dir(&b).arg(format!("-DLibSel4TestPrinterRegex={regex}")).arg(".");
        python_env(&mut c);
        run(&mut c);
    }
    let mut c = Command::new("ninja");
    c.current_dir(&b);
    python_env(&mut c);
    run(&mut c);
    b
}

/// sel4test cases that measure wall-clock scheduling behaviour and fail on
/// a loaded host, or on upstream seL4 itself: SCHED0014 fails 20 runs in
/// 20 on seL4 with 4 cores in kvm-reduced (DESIGN.md §12). A run whose
/// only failures are among these reruns them alone, up to three times.
const TIMING_TESTS: &[&str] = &["SCHED0011", "SCHED0014", "TIMEOUTFAULT0001"];

fn sel4test(o: &Opts, fl4test: bool) {
    if !fl4test && env::var_os("FL4_TESTS").is_none() {
        if let Err(failed) = sel4test_once(o, false) {
            if failed.is_empty() || !failed.iter().all(|f| TIMING_TESTS.contains(&f.as_str())) {
                fail("sel4test failed");
            }
            for attempt in 1..=3 {
                let regex = format!("^({})$", failed.join("|"));
                eprintln!("xtask: rerunning timing-sensitive {} (attempt {attempt} of 3)", failed.join(", "));
                env::set_var("FL4_TESTS", &regex);
                let r = sel4test_once(o, false);
                env::remove_var("FL4_TESTS");
                if r.is_ok() {
                    eprintln!("xtask: sel4test passed after rerunning {}", failed.join(", "));
                    return;
                }
            }
            fail("sel4test failed");
        }
        return;
    }
    if sel4test_once(o, fl4test).is_err() {
        fail(&format!("{} failed", if fl4test { "fl4test" } else { "sel4test" }));
    }
}

/// Differential fuzzing (DESIGN.md §12): run fl4test/fuzz.c's generated
/// programs on upstream seL4 and on FL4 and compare their traces.
fn fuzz(o: &Opts) {
    let mut traces = Vec::new();
    for kernel in ["sel4", "fl4"] {
        env::set_var("FL4_KERNEL", kernel);
        env::set_var("FL4_TESTS", "^FL4FUZZ0001$");
        let b = sel4test_build(o, false);
        if sel4test_once(o, false).is_err() {
            fail(&format!("the fuzz programs did not finish on {kernel}"));
        }
        let log = fs::read_to_string(b.join("sel4test.log")).unwrap();
        let lines: Vec<String> = log.lines().filter(|l| l.starts_with("FUZZ ")).map(|l| l.trim_end().to_string()).collect();
        eprintln!("xtask: fuzz: {} trace lines from {kernel}", lines.len());
        traces.push(lines);
    }
    env::remove_var("FL4_KERNEL");
    env::remove_var("FL4_TESTS");
    let (a, b) = (&traces[0], &traces[1]);
    let mut diffs = 0;
    for i in 0..a.len().max(b.len()) {
        let (x, y) = (a.get(i).map(String::as_str).unwrap_or("<none>"), b.get(i).map(String::as_str).unwrap_or("<none>"));
        if x != y {
            if diffs < 20 {
                eprintln!("  seL4: {x}\n  FL4:  {y}");
            }
            diffs += 1;
        }
    }
    if a.is_empty() || diffs > 0 {
        fail(&format!("fuzz: {diffs} of {} trace lines differ", a.len()));
    }
    eprintln!("xtask: fuzz: {} trace lines, seL4 and FL4 agree", a.len());
}

/// One run; Err holds the failed tests' names (empty if the run did not
/// complete).
/// Multiboot 2 through GRUB on UEFI firmware (OVMF), under KVM (GitHub
/// issue #8): the kernel must find ACPI from the RSDP the bootloader
/// passes, start every core, and start the root task. That is where this
/// check ends: sel4test's driver cannot go further on UEFI, because its
/// timer set-up looks for the RSDP in the BIOS areas from user space.
/// AArch64: boot sel4test's image through UEFI with ACPI (no device tree)
/// on GICv3 and check the kernel finds the cores and starts the root task.
fn uefi_aarch64(o: &Opts) {
    let b = sel4test_build(o, false);
    let dir = root().join("build/uefi-aarch64");
    fs::create_dir_all(&dir).unwrap();
    let esp = aarch64_esp(&b.join("images/sel4test-driver-image-arm-qemu-arm-virt"), &dir);
    let smp = o.smp.max(1);
    let setup = if o.setup == "tcg" { "tcg-acpi" } else { o.setup.as_str() };
    let out = run_qemu(qemu_cmd_aarch64(setup, smp, &esp), 300, &["FL4: starting the root task", "FL4 boot failed", "FL4 panic"], &dir.join("serial.log"));
    for l in out.lines().filter(|l| l.contains("FL4")) {
        eprintln!("xtask: uefi: {}", l.trim_end());
    }
    if !out.contains("hardware from the ACPI") || !out.contains(&format!("FL4: {smp} core(s) running")) || !out.contains("FL4: starting the root task") {
        fail("UEFI boot did not reach the root task");
    }
    eprintln!("xtask: uefi: booted through UEFI with ACPI on {smp} core(s)");
}

fn uefi(o: &Opts) {
    if aarch64(o) {
        return uefi_aarch64(o);
    }
    let b = sel4test_build(o, false);
    let dir = root().join("build/uefi");
    let esp = dir.join("esp/EFI/BOOT");
    let _ = fs::remove_dir_all(dir.join("esp"));
    fs::create_dir_all(&esp).unwrap();
    let cfg = dir.join("grub.cfg");
    let script = "set timeout=0\nserial --unit=0 --speed=115200\nterminal_output serial\n\
                  menuentry fl4 {\n  multiboot2 /boot/kernel\n  module2 /boot/rootserver\n  boot\n}\n";
    fs::write(&cfg, script).unwrap();
    run(Command::new("grub-mkstandalone")
        .args([
            "-O", "x86_64-efi", "--locales=", "--fonts=",
            "--install-modules=multiboot2 serial terminal normal memdisk tar",
            "--modules=multiboot2 serial terminal normal", "-o",
        ])
        .arg(esp.join("BOOTX64.EFI"))
        .arg(format!("boot/grub/grub.cfg={}", cfg.display()))
        .arg(format!("boot/kernel={}", b.join("images/kernel-x86_64-pc99").display()))
        .arg(format!("boot/rootserver={}", b.join("images/sel4test-driver-image-x86_64-pc99").display())));
    let log = dir.join("serial.log");
    let _ = fs::remove_file(&log);
    let smp = o.smp.max(1);
    let mut q = Command::new("qemu-system-x86_64")
        .args(["-enable-kvm", "-machine", "q35,kernel-irqchip=split", "-cpu", "host,+invtsc", "-m", "3G", "-smp"])
        .arg(smp.to_string())
        .args(["-bios", "/usr/share/ovmf/OVMF.fd", "-display", "none", "-monitor", "none", "-no-reboot", "-serial"])
        .arg(format!("file:{}", log.display()))
        .arg("-drive")
        .arg(format!("format=raw,file=fat:rw:{}", dir.join("esp").display()))
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(120);
    let text = loop {
        std::thread::sleep(std::time::Duration::from_millis(500));
        let t = String::from_utf8_lossy(&fs::read(&log).unwrap_or_default()).to_string();
        let done = t.contains("FL4: starting the root task") || t.contains("boot failed") || q.try_wait().unwrap().is_some();
        if done || std::time::Instant::now() > deadline {
            break t;
        }
    };
    let _ = q.kill();
    let _ = q.wait();
    for l in text.lines().filter(|l| l.starts_with("FL4")) {
        eprintln!("xtask: uefi: {l}");
    }
    if !text.contains(&format!("FL4: {smp} core(s)")) || !text.contains("FL4: starting the root task") {
        fail("UEFI boot did not reach the root task");
    }
    eprintln!("xtask: uefi: booted through GRUB Multiboot 2 on OVMF with {smp} core(s)");
}

fn sel4test_once(o: &Opts, fl4test: bool) -> Result<(), Vec<String>> {
    let b = sel4test_build(o, fl4test);
    let log = b.join("sel4test.log");
    let stop = ["All is well in the universe", "Test suite failed", "Halting...", "FL4 panic", "FL4 boot failed:", "FL4: halted"];
    let out = if aarch64(o) {
        let esp = aarch64_esp(&b.join("images/sel4test-driver-image-arm-qemu-arm-virt"), &b);
        run_qemu(qemu_cmd_aarch64(&o.setup, o.smp, &esp), o.timeout, &stop, &log)
    } else {
        let k = b.join("images/kernel-x86_64-pc99");
        let i = b.join("images/sel4test-driver-image-x86_64-pc99");
        run_qemu(qemu_cmd(&o.setup, o.smp, &k, Some(&i)), o.timeout, &stop, &log)
    };
    if let Ok(expected) = env::var("FL4_EXPECT_VM") {
        if !vm_expectation_ok(&out, &expected) {
            eprintln!("xtask: expected virtualization {expected}; inspect the CPU mitigation diagnostic in {}", log.display());
            return Err(Vec::new());
        }
        if expected == "ap-rejected" {
            eprintln!("xtask: incompatible AP halted boot before userspace");
            return Ok(());
        }
    }
    let (passed, failed) = sel4test_results(&out);
    let suite = if fl4test { "fl4test" } else { "sel4test" };
    eprintln!("\nxtask: {suite} {}: {passed} passed, {} failed", o.setup, failed.len());
    for f in &failed {
        eprintln!("  {f}");
    }
    let finished = out.contains("All is well in the universe") || out.contains("Test suite failed");
    if !finished {
        eprintln!("xtask: {suite} did not complete");
        return Err(Vec::new());
    }
    // The driver's own "Test all tests ran" fails along with any test.
    let failed: Vec<String> = failed.into_iter().filter(|f| !f.contains("all tests ran")).collect();
    if !failed.is_empty() || !out.contains("All is well in the universe") {
        return Err(failed);
    }
    Ok(())
}

/// Explicitly distinguish guest execution from an unavailable-backend skip.
fn vm_expectation_ok(out: &str, expected: &str) -> bool {
    match expected {
        "present" => (out.contains("FL4: virtualization AMD-V") || out.contains("FL4: virtualization VT-x"))
            && !out.contains("Virtualization unavailable; skipping guest execution"),
        "absent" => out.contains("FL4: virtualization unavailable"),
        "ap-rejected" => (out.contains("FL4: virtualization AMD-V") || out.contains("FL4: virtualization VT-x"))
            && out.contains("FL4: rejecting AP with APIC id ")
            && out.contains("FL4 boot failed: incompatible AP capabilities; refusing to start userspace")
            && !out.contains("FL4: starting the root task"),
        _ => false,
    }
}

/// Passed tests and failed test names. Release builds print only
/// "Starting test N: NAME" and the errors, so a failure belongs to the
/// test that started last.
fn sel4test_results(out: &str) -> (usize, Vec<String>) {
    let mut failed: Vec<String> = Vec::new();
    let mut current: Option<String> = None;
    let mut passed = 0;
    for l in out.lines() {
        // Some guest printers emit LF-CR rather than CR-LF. Keep the
        // leading tab on error lines, but remove the preceding CR.
        let l = l.trim_end().trim_start_matches('\r');
        if let Some(rest) = l.strip_prefix("Starting test ") {
            current = rest.split(": ").nth(1).map(|n| n.to_string());
        } else if l.starts_with("Test ") && l.ends_with(" passed") {
            passed += 1;
        } else if let Some(i) = l.find(" tests passed") {
            // The suite summary, "... N tests passed" or "... M/N tests passed".
            let n = l[..i].rsplit([' ', '/']).nth(if l[..i].contains('/') { 1 } else { 0 });
            if let Some(n) = n.and_then(|n| n.parse().ok()) {
                passed = n;
            }
        } else if l.starts_with("\tError:") || l.starts_with("\tFailure:") || (l.starts_with("Test ") && l.ends_with(" failed")) {
            if let Some(c) = &current {
                if !failed.contains(c) {
                    failed.push(c.clone());
                }
            }
        }
    }
    (passed, failed)
}

/// Deterministic simulation (DESIGN.md §10). Each campaign replays
/// crates/fl4-sim/regressions first, then runs --seeds seeds (default 200)
/// on --smp cores (default 4): serially, 20000 steps each; with the cores'
/// kernel entries interleaved (transactions, 8000 steps), under the random
/// scheduler and under PCT; and interleaved again with every entry under
/// the serial gate.
fn sim(o: &Opts) {
    let r = root();
    run(Command::new("cargo").current_dir(&r).args(["build", "--release", "-p", "fl4-sim"]));
    // The same campaign with every entry under the serial gate, the
    // test-only differential configuration.
    let dir = r.join("target/serial-gate");
    run(Command::new("cargo").current_dir(&r).args(["build", "--release", "-p", "fl4-sim", "--features", "serial-gate", "--target-dir"]).arg(&dir));
    let cores = if o.smp > 1 { o.smp } else { 4 };
    let (seeds, cores) = (o.seeds.to_string(), cores.to_string());
    let base = ["--seeds", seeds.as_str(), "--cores", cores.as_str()];
    // Both at once: each runs its seeds in child processes, one per host
    // CPU, so together they keep the host busy until both are done.
    let mut gate = Command::new(dir.join("release/fl4-sim")).args(base).args(["--steps", "8000", "--conc"]).spawn().unwrap();
    // Every campaign of DESIGN.md §10: random, PCT and x86-TSO schedules,
    // the targeted endpoint and notification races, and the bounded
    // exhaustive search.
    let suite = Command::new(r.join("target/release/fl4-sim")).args(base).arg("--suite").status().unwrap();
    let gate = gate.wait().unwrap();
    if !suite.success() || !gate.success() {
        fail("the simulator found failures");
    }
}

/// Mutation testing (DESIGN.md §10): each known-broken runtime must fail
/// seeds of a 100-seed concurrent campaign under at least one of the
/// schedulers (random, PCT, random on the x86-TSO store-buffer model); the
/// catch rate of each is reported.
fn mutants() {
    let r = root();
    let mut ok = true;
    // A clear_free without validation needs two cores resetting the same
    // untyped, which the simulated workload (one root task) never does:
    // fl4-store's own concurrent test must catch it.
    let caught = !Command::new("cargo")
        .current_dir(&r)
        .args(["test", "--quiet", "-p", "fl4-store", "--features", "mutant-clear-no-validate", "clear_free"])
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .unwrap()
        .success();
    eprintln!("xtask: mutant-clear-no-validate (fl4-store test): {}", if caught { "caught" } else { "survived" });
    ok &= caught;
    for m in ["mutant-skip-validation", "mutant-no-publish", "mutant-gate-no-wait", "mutant-gate-release"] {
        let dir = r.join("target").join(m);
        run(Command::new("cargo").current_dir(&r).args(["build", "--quiet", "--release", "-p", "fl4-sim", "--features", m, "--target-dir"]).arg(&dir));
        let mut caught = false;
        for sched in [&["--conc"][..], &["--conc", "--pct", "3"][..], &["--tso"][..]] {
            let out = Command::new(dir.join("release/fl4-sim"))
                .args(["--seeds", "100", "--cores", "4", "--steps", "4000", "--timeout", "60", "--no-shrink"])
                .args(sched)
                .output()
                .unwrap();
            let text = String::from_utf8_lossy(&out.stdout);
            let failed = text.lines().filter(|l| l.contains("failed:") && l.starts_with("fl4-sim: seed")).count();
            let name = sched[1..].first().map_or(if sched[0] == "--tso" { "TSO" } else { "random" }, |_| "PCT");
            eprintln!("xtask: {m} ({name}): {failed}/100 seeds fail");
            caught |= failed > 0;
        }
        ok &= caught;
    }
    if !ok {
        fail("a mutant survived the simulator");
    }
}

/// The trusted base (TRUSTED, DESIGN.md §9): every listed path exists;
/// prints the lines of source in each group and in all.
fn trusted() {
    let r = root();
    let list = fs::read_to_string(r.join("TRUSTED")).unwrap();
    let mut groups: Vec<(String, usize)> = Vec::new();
    for l in list.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#')) {
        let (g, p) = l.split_once(':').unwrap_or_else(|| fail(&format!("TRUSTED: bad line {l:?}")));
        let path = r.join(p.trim());
        if !path.exists() {
            fail(&format!("TRUSTED: {} does not exist", p.trim()));
        }
        let n = source_lines(&path);
        match groups.iter_mut().find(|(name, _)| name == g.trim()) {
            Some((_, total)) => *total += n,
            None => groups.push((g.trim().to_string(), n)),
        }
    }
    for (g, n) in &groups {
        eprintln!("xtask: trusted {g}: {n} lines");
    }
    eprintln!("xtask: trusted base: {} lines", groups.iter().map(|(_, n)| n).sum::<usize>());
}

/// Lines in a source file, or in every source file under a directory.
fn source_lines(p: &Path) -> usize {
    if p.is_dir() {
        let mut n = 0;
        for e in fs::read_dir(p).unwrap() {
            n += source_lines(&e.unwrap().path());
        }
        return n;
    }
    match p.extension().and_then(|e| e.to_str()) {
        Some("rs" | "S" | "lean" | "ld") => fs::read_to_string(p).map(|t| t.lines().count()).unwrap_or(0),
        _ => 0,
    }
}

/// The extractability gate (DESIGN.md §6): all of fl4-core goes through
/// Charon and Aeneas without errors, the result typechecks in Lean, and so
/// do the proofs about it. `extract` already fails on any Aeneas error.
fn gate() {
    extract();
    // proofs/lakefile.lean requires Aeneas's Lean library from .deps/aeneas.
    let link = root().join("proofs/.deps/aeneas");
    if !link.exists() {
        fs::create_dir_all(link.parent().unwrap()).unwrap();
        std::os::unix::fs::symlink(deps().join("aeneas/backends/lean"), &link).unwrap();
    }
    // P0: constant values, then a theorem per function (DESIGN.md §9).
    let scripts = root().join("xtask/scripts");
    for g in ["gen_const_specs.py", "gen_p0.py"] {
        run(Command::new("python3").arg(scripts.join(g)).arg(root().join("proofs")));
    }
    let mut c = Command::new("lake");
    c.current_dir(root().join("proofs")).arg("build");
    run(&mut c);
    let status = fs::read_to_string(root().join("proofs/Fl4Proofs/P0/status.json")).unwrap();
    let left = status.matches("\"sorry\": {}").count() == 0;
    eprintln!("xtask: gate passed (proofs/Fl4Proofs/P0/status.json lists the P0 theorems still to prove)");
    if left && env::var_os("FL4_P0_STRICT").is_some() {
        fail("P0 is not complete");
    }
}

fn extract() {
    let r = root();
    let d = deps().join("aeneas");
    let charon = d.join("charon/bin/charon");
    let aeneas = d.join("bin/aeneas");
    let out = r.join("build/llbc");
    fs::create_dir_all(&out).unwrap();
    run(Command::new(&charon).current_dir(r.join("crates/fl4-core")).args(["cargo", "--preset=aeneas", "--include", "fl4_abi", "--dest"]).arg(&out));
    run(Command::new(&aeneas).args(["-backend", "lean", "-split-files", "-dest"]).arg(r.join("proofs/Fl4Core")).arg(out.join("fl4_core.llbc")));
    // Aeneas can leave spaces at the end of wrapped binder lists.
    for name in ["Types.lean", "Funs.lean", "FunsExternal_Template.lean"] {
        let path = r.join("proofs/Fl4Core").join(name);
        let text = fs::read_to_string(&path).unwrap();
        let clean = text.lines().map(str::trim_end).collect::<Vec<_>>().join("\n") + "\n";
        fs::write(path, clean).unwrap();
    }
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let cmd = args.first().cloned().unwrap_or_default();
    let o = parse(&args[1.min(args.len())..]);
    match cmd.as_str() {
        "kernel" => {
            build_kernel(&o);
        }
        "run" if aarch64(&o) => {
            let root_elf = o.rest.first().map(PathBuf::from).unwrap_or_else(|| fail("usage: cargo xtask run --arch aarch64 <root task ELF>"));
            let image = build_aarch64_image(&o, &root_elf);
            let esp = aarch64_esp(&image, &root().join("build/aarch64"));
            run_qemu(qemu_cmd_aarch64(&o.setup, o.smp, &esp), o.timeout, &["FL4: halted", "FL4 panic", "FL4 boot failed"], &root().join("build/run.log"));
        }
        "run" => {
            let k = build_kernel(&o);
            let initrd = o.rest.first().map(PathBuf::from);
            run_qemu(qemu_cmd(&o.setup, o.smp, &k, initrd.as_deref()), o.timeout, &["FL4 halted", "FL4 panic"], &root().join("build/run.log"));
        }
        "sel4test-build" => {
            sel4test_build(&o, false);
        }
        "sel4test" => sel4test(&o, false),
        "fl4test" => sel4test(&o, true),
        "uefi" => uefi(&o),
        "extract" => extract(),
        "gate" => gate(),
        "sim" => sim(&o),
        "mutants" => mutants(),
        "fuzz" => fuzz(&o),
        "trusted" => trusted(),
        "bench" => bench(&o),
        "kbench" => kbench(&o),
        _ => {
            eprintln!("usage: cargo xtask <kernel|run|sel4test-build|sel4test|fl4test|uefi|extract|gate|sim|mutants|fuzz|trusted|bench [fl4|sel4]|kbench> [--arch x86_64|aarch64] [--release] [--setup kvm|kvm-reduced|tcg|...] [--smp N] [--timeout S] [--seeds N]");
            exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::sel4test_results;
    use super::vm_expectation_ok;

    #[test]
    fn virtualization_expectations_reject_silently_skipped_guest_tests() {
        let present = "FL4: virtualization AMD-V\nAll is well in the universe";
        let absent = "FL4: virtualization unavailable\nVirtualization unavailable; skipping guest execution";
        assert!(vm_expectation_ok(present, "present"));
        assert!(!vm_expectation_ok(absent, "present"));
        assert!(!vm_expectation_ok("", "present"));
        assert!(vm_expectation_ok(absent, "absent"));
        assert!(!vm_expectation_ok(present, "absent"));
        assert!(!vm_expectation_ok(present, "typo"));
    }

    #[test]
    fn ap_rejection_requires_bsp_shutdown_before_userspace() {
        let ap_only = "FL4: virtualization AMD-V\nFL4: rejecting AP with APIC id 1: speculation capabilities differ between cores\n";
        assert!(!vm_expectation_ok(ap_only, "ap-rejected"));
        let stopped = format!("{ap_only}FL4 boot failed: incompatible AP capabilities; refusing to start userspace\n");
        assert!(vm_expectation_ok(&stopped, "ap-rejected"));
        assert!(!vm_expectation_ok(&format!("{stopped}FL4: starting the root task"), "ap-rejected"));
        assert!(!vm_expectation_ok("FL4 panic: speculation capabilities differ between cores", "ap-rejected"));
    }

    #[test]
    fn debug_log() {
        let log = "Starting test 1: A\nRunning test A (x)\nTest A passed\nStarting test 2: B\n\tError: x at line 1\nTest B failed\nTest suite failed. 1/2 tests passed.\n";
        assert_eq!(sel4test_results(log), (1, vec!["B".to_string()]));
    }

    #[test]
    fn release_log() {
        let log = "Starting test 95: A\nStarting test 96: B\n\tFailure: result == SUCCESS at line 296 of file d/sel4test-driver/src/testtypes.c\nStarting test 97: C\nTest suite failed. 170/171 tests passed.\n";
        assert_eq!(sel4test_results(log), (170, vec!["B".to_string()]));
        let lfcr = log.replace('\n', "\n\r");
        assert_eq!(sel4test_results(&lfcr), (170, vec!["B".to_string()]));
    }
}
