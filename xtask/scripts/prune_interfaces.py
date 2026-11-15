#!/usr/bin/env python3
# One-time import step: drop methods and interfaces from seL4's interface XML
# whose <condition> is false under FL4's fixed configuration (DESIGN.md §3).
# Conditions on profile-dependent settings (debug build, printing, hardware
# debug API, SMP) are kept; the generators evaluate those per profile.
import re, sys, xml.dom.minidom

FIXED = {
    'CONFIG_KERNEL_MCS': True, 'CONFIG_VTX': True, 'CONFIG_IOMMU': False,
    'CONFIG_ARCH_IA32': False, 'CONFIG_X86_64_VTX_64BIT_GUESTS': True,
    'CONFIG_ENABLE_BENCHMARKS': False, 'CONFIG_BENCHMARK_TRACK_UTILISATION': False,
    'CONFIG_DANGEROUS_CODE_INJECTION': False, 'CONFIG_KERNEL_X86_DANGEROUS_MSR': False,
    'CONFIG_ARM_HYPERVISOR_SUPPORT': False, 'CONFIG_ARM_SMMU': False,
    'CONFIG_TK1_SMMU': False, 'CONFIG_ALLOW_SMC_CALLS': False,
}

def ev(node):
    """Evaluate a condition node; None means 'depends on the profile'."""
    if node.nodeType != node.ELEMENT_NODE:
        return None
    t = node.tagName
    kids = [k for k in node.childNodes if k.nodeType == k.ELEMENT_NODE]
    if t == 'config':
        return FIXED.get(node.getAttribute('var'))
    if t == 'not':
        v = ev(kids[0]); return None if v is None else not v
    if t in ('and', 'or'):
        vs = [ev(k) for k in kids]
        if t == 'and':
            if False in vs: return False
            return True if all(v is True for v in vs) else None
        if True in vs: return True
        return False if all(v is False for v in vs) else None
    if t == 'condition':
        return ev(kids[0]) if kids else True
    raise ValueError(t)

def cond_of(block):
    m = re.match(r'\s*<(method|interface|config)\b[^>]*>\s*(<condition>.*?</condition>)', block, re.S)
    if not m:
        return True
    return ev(xml.dom.minidom.parseString(m.group(2)).documentElement)

def prune(text, tag):
    out, pos = [], 0
    pat = re.compile(r'[ \t]*<%s[ >].*?</%s>[ \t]*\n?' % (tag, tag), re.S)
    for m in pat.finditer(text):
        out.append(text[pos:m.start()])
        if cond_of(m.group(0)) is not False:
            out.append(m.group(0))
        pos = m.end()
    out.append(text[pos:])
    return ''.join(out)

for path in sys.argv[1:]:
    s = open(path).read()
    if '<syscalls>' in s:
        # FL4 is MCS only; the non-MCS section stays, empty, because
        # bindings generators such as rust-sel4's sel4-sys require it.
        s = re.sub(r'<api-master>.*?</api-master>', '<api-master/>', s, flags=re.S)
        s = prune(s, 'config')
    else:
        s = prune(prune(s, 'interface'), 'method')
    open(path, 'w').write(s)
