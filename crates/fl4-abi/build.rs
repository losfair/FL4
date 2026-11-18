//! Generates FL4's ABI numbering from the one interface definition in
//! `interfaces/` (DESIGN.md §2). The numbering follows the same rules as
//! seL4's `invocation_header_gen.py` and `syscall_header_gen.py`, which also
//! generate FL4's libsel4 from the same files, so kernel and user space
//! always agree.
//!
//! The configuration comes from the `gen_config.json` that the CMake drop-in
//! writes (`FL4_GEN_CONFIG`), or from the built-in defaults for a standalone
//! build. Only the settings that conditions in the XML test matter here.

use std::collections::{BTreeMap, HashSet};
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

type Config = BTreeMap<String, serde_json::Value>;

fn default_config(debug: bool) -> Config {
    let mut c = Config::new();
    let b = |v: bool| serde_json::Value::Bool(v);
    c.insert("KERNEL_MCS".into(), b(true));
    c.insert("VTX".into(), b(true));
    c.insert("X86_64_VTX_64BIT_GUESTS".into(), b(true));
    c.insert("DEBUG_BUILD".into(), b(debug));
    c.insert("PRINTING".into(), b(debug));
    c.insert("HARDWARE_DEBUG_API".into(), b(debug));
    c.insert("KERNEL_INVOCATION_REPORT_ERROR_IPC".into(), b(debug));
    c.insert("IRQ_REPORTING".into(), b(debug));
    c.insert("ENABLE_SMP_SUPPORT".into(), b(true));
    c.insert("SET_TLS_BASE_SELF".into(), b(true));
    c.insert("KERNEL_X86_DANGEROUS_MSR".into(), b(false));
    c.insert("EXPORT_PMC_USER".into(), b(false));
    c.insert("NUM_DOMAINS".into(), "1".into());
    c.insert("NUM_DOMAIN_SCHEDULES".into(), "2".into());
    c.insert("MAX_NUM_NODES".into(), "64".into());
    c.insert("ROOT_CNODE_SIZE_BITS".into(), "13".into());
    c
}

fn cfg_bool(c: &Config, k: &str) -> bool {
    match c.get(k) {
        Some(serde_json::Value::Bool(b)) => *b,
        Some(serde_json::Value::String(s)) => s != "0" && !s.is_empty(),
        _ => false,
    }
}

fn cfg_u64(c: &Config, k: &str) -> u64 {
    match c.get(k) {
        Some(serde_json::Value::String(s)) => s.parse().unwrap_or_else(|_| panic!("{k}={s}")),
        Some(serde_json::Value::Number(n)) => n.as_u64().unwrap(),
        v => panic!("missing numeric config {k}: {v:?}"),
    }
}

fn eval(c: &Config, n: roxmltree::Node) -> bool {
    let kids: Vec<_> = n.children().filter(|k| k.is_element()).collect();
    match n.tag_name().name() {
        "condition" => kids.first().map_or(true, |k| eval(c, *k)),
        "config" => {
            let var = n.attribute("var").unwrap();
            cfg_bool(c, var.strip_prefix("CONFIG_").unwrap_or(var))
        }
        "not" => !eval(c, kids[0]),
        "and" => kids.iter().all(|k| eval(c, *k)),
        "or" => kids.iter().any(|k| eval(c, *k)),
        t => panic!("unknown condition element {t}"),
    }
}

/// Method condition, as seL4's generator sees it: only `<condition>`
/// elements inside the method itself.
fn method_condition<'a>(m: roxmltree::Node<'a, 'a>) -> Option<roxmltree::Node<'a, 'a>> {
    m.descendants().find(|d| d.has_tag_name("condition"))
}

fn labels(c: &Config, path: &Path, out: &mut Vec<String>, disabled: &mut Vec<String>) {
    let text = fs::read_to_string(path).unwrap();
    let doc = roxmltree::Document::parse(&text).unwrap();
    let mut seen = HashSet::new();
    for m in doc.descendants().filter(|n| n.has_tag_name("method")) {
        let id = m.attribute("id").unwrap().to_string();
        let cond = method_condition(m);
        let key = format!("{id}/{:?}", cond.map(|n| text[n.range()].to_string()));
        if !seen.insert(key) {
            continue;
        }
        if cond.map_or(true, |n| eval(c, n)) {
            out.push(id);
        } else {
            disabled.push(id);
        }
    }
}

/// Syscalls in configuration order; disabled ones get `i64::MIN`, a number
/// no caller can pass (their positional number stays unused).
fn syscalls(c: &Config, path: &Path) -> Vec<(String, i64)> {
    let text = fs::read_to_string(path).unwrap();
    let doc = roxmltree::Document::parse(&text).unwrap();
    let mut v = Vec::new();
    let mut n = -1i64;
    for section in ["api-mcs", "debug"] {
        let s = doc.descendants().find(|e| e.has_tag_name(section)).unwrap();
        for config in s.children().filter(|e| e.has_tag_name("config")) {
            let cond = config.children().find(|e| e.has_tag_name("condition"));
            let on = cond.map_or(true, |k| eval(c, k));
            for sc in config.children().filter(|e| e.has_tag_name("syscall")) {
                // Numbers are positional whatever the condition, as in
                // syscall_header_gen.py.
                v.push((sc.attribute("name").unwrap().to_string(), if on { n } else { i64::MIN }));
                n -= 1;
            }
        }
    }
    v
}

fn main() {
    let root = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap()).join("../..");
    let ifaces = root.join("interfaces");
    println!("cargo:rerun-if-changed={}", ifaces.display());
    println!("cargo:rerun-if-env-changed=FL4_GEN_CONFIG");
    let debug = env::var("CARGO_FEATURE_RELEASE_PROFILE").is_err();
    let config = match env::var("FL4_GEN_CONFIG") {
        Ok(p) => {
            println!("cargo:rerun-if-changed={p}");
            let mut c = default_config(debug);
            let user: Config = serde_json::from_str(&fs::read_to_string(&p).unwrap()).unwrap();
            c.extend(user);
            c
        }
        Err(_) => default_config(debug),
    };

    let mut o = String::new();
    o.push_str("// Generated by fl4-abi/build.rs from interfaces/. Do not edit.\n\n");

    // Invocation labels: generic, then sel4_arch, then arch, as in seL4.
    let mut all = vec!["InvalidInvocation".to_string()];
    let mut disabled = Vec::new();
    labels(&config, &ifaces.join("object-api.xml"), &mut all, &mut disabled);
    let n_generic = all.len();
    labels(&config, &ifaces.join("object-api-sel4-arch-x86_64.xml"), &mut all, &mut disabled);
    let n_sel4_arch = all.len();
    labels(&config, &ifaces.join("object-api-arch-x86.xml"), &mut all, &mut disabled);
    labels(&config, &ifaces.join("object-api-extensions.xml"), &mut all, &mut disabled);
    writeln!(o, "/// Invocation labels (`seL4_MessageInfo` label field).").unwrap();
    writeln!(o, "#[allow(non_upper_case_globals)]\npub mod label {{").unwrap();
    for (i, l) in all.iter().enumerate() {
        writeln!(o, "    pub const {l}: u64 = {i};").unwrap();
    }
    // Methods this configuration leaves out: no message carries them.
    for l in &disabled {
        if !all.contains(l) {
            writeln!(o, "    pub const {l}: u64 = u64::MAX;").unwrap();
        }
    }
    writeln!(o, "    pub const nInvocationLabels: u64 = {n_generic};").unwrap();
    writeln!(o, "    pub const nSeL4ArchInvocationLabels: u64 = {n_sel4_arch};").unwrap();
    writeln!(o, "    pub const nArchInvocationLabels: u64 = {};", all.len()).unwrap();
    writeln!(o, "}}\n").unwrap();

    writeln!(o, "/// System call numbers (`rdx` on x86_64).").unwrap();
    writeln!(o, "#[allow(non_upper_case_globals)]\npub mod syscall {{").unwrap();
    let sc = syscalls(&config, &ifaces.join("syscall.xml"));
    let n_api = 11;
    for (name, n) in &sc {
        writeln!(o, "    pub const Sys{name}: i64 = {n};").unwrap();
    }
    // The bench profile's syscalls, numbers that never match when absent.
    for name in ["X86DangerousWRMSR", "X86DangerousRDMSR"] {
        if !sc.iter().any(|(n, _)| n == name) {
            writeln!(o, "    pub const Sys{name}: i64 = i64::MIN;").unwrap();
        }
    }
    writeln!(o, "    pub const SYSCALL_MAX: i64 = -1;").unwrap();
    writeln!(o, "    pub const SYSCALL_MIN: i64 = -{n_api};").unwrap();
    writeln!(o, "}}\n").unwrap();

    writeln!(o, "/// Settings read from the user-program configuration (DESIGN.md §3).").unwrap();
    writeln!(o, "pub mod config {{").unwrap();
    for k in ["DEBUG_BUILD", "PRINTING", "HARDWARE_DEBUG_API", "KERNEL_INVOCATION_REPORT_ERROR_IPC", "IRQ_REPORTING", "ENABLE_SMP_SUPPORT", "SET_TLS_BASE_SELF", "KERNEL_X86_DANGEROUS_MSR", "EXPORT_PMC_USER"] {
        writeln!(o, "    pub const {k}: bool = {};", cfg_bool(&config, k)).unwrap();
    }
    for k in ["NUM_DOMAINS", "NUM_DOMAIN_SCHEDULES", "MAX_NUM_NODES", "ROOT_CNODE_SIZE_BITS"] {
        writeln!(o, "    pub const {k}: u64 = {};", cfg_u64(&config, k)).unwrap();
    }
    writeln!(o, "}}").unwrap();

    let out = PathBuf::from(env::var("OUT_DIR").unwrap()).join("generated.rs");
    fs::write(out, o).unwrap();
}
