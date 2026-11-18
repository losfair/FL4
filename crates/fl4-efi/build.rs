//! Embed the kernel image (FL4_KERNEL_ELF, required) and optionally a
//! root task (FL4_ROOTSERVER_ELF) in the loader.
use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-env-changed=FL4_KERNEL_ELF");
    println!("cargo:rerun-if-env-changed=FL4_ROOTSERVER_ELF");
    let out = PathBuf::from(env::var("OUT_DIR").unwrap());
    let mut s = String::new();
    match env::var("FL4_KERNEL_ELF") {
        Ok(p) => {
            println!("cargo:rerun-if-changed={p}");
            s += &format!("pub static KERNEL: &[u8] = include_bytes!({p:?});\n");
        }
        Err(_) => s += "pub static KERNEL: &[u8] = &[];\n",
    }
    match env::var("FL4_ROOTSERVER_ELF") {
        Ok(p) if !p.is_empty() => {
            println!("cargo:rerun-if-changed={p}");
            s += &format!("pub static ROOTSERVER: &[u8] = include_bytes!({p:?});\n");
        }
        _ => s += "pub static ROOTSERVER: &[u8] = &[];\n",
    }
    if env::var("CARGO_CFG_TARGET_ARCH").as_deref() == Ok("x86_64") {
        println!("cargo:rerun-if-env-changed=FL4_BOOT_MODULE");
        if let Ok(p) = env::var("FL4_BOOT_MODULE") {
            println!("cargo:rerun-if-changed={p}");
            s += &format!("pub static MODULE: &[u8] = include_bytes!({p:?});\n");
        } else {
            s += "pub static MODULE: &[u8] = &[];\n";
        }
    }
    fs::write(out.join("embedded.rs"), s).unwrap();
}
