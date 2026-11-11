#!/usr/bin/env python3
"""Aggregate module/line counts (and, if available, reached-declaration counts) by proof stage.

Usage: python3 -I stage_sizes.py <graph_dir> [<audit_dir>]
The directory→stage assignment is this review's reading of directory names, module
docstrings and the top-level call chain; it is a heuristic map, not a proof artefact.
"""
import csv
import os
import sys

graph, audit = sys.argv[1], (sys.argv[2] if len(sys.argv) > 2 else None)
STAGES = {
    "S0 public spec + bridges": ["PublicTheory", "PublicWilson", "ChallengeSpec", "Challenge", "ContactSpec",
        "PublicView", "WilsonBridge", "HierarchyBridge", "TraceBridge", "ContactBridge", "Construction",
        "Solution", "ConcreteSU2", "YM.Nonperturbative", "YM.Independent", "YM.Spec", "YM.Examples", "YM"],
    "S1 lattice/gauge foundations, labels, lattice representatives": ["YM.Gauge", "YM.Lattice", "YM.Wilson",
        "YM.Labels", "YM.Source", "YM.Euclid", "YM.Cells", "YM.Space", "YM.Axis", "YM.Shift", "YM.Price",
        "YM.Primitives", "YM.CellFourier", "YM.Compact", "YM.Exterior", "YM.Tree", "YM.Lane", "YM.Marker"],
    "S2 multiscale RG / UV control (block-spin, polymer, Gaussian steps)": ["YM.RG", "YM.RG05Readout", "YM.RG08",
        "YM.RG12", "YM.Push", "YM.Next", "YM.PhysicalNext", "YM.AnalyticNext", "YM.AnalyticBridge",
        "YM.UVExtension", "YM.UVNext", "YM.UVExt", "YM.MergeProof", "YM.Further", "YM.Extra", "YM.Planned",
        "YM.Progress", "YM.RemainderComparison", "YM.SectorNext", "YM.SectorTools", "YM.ProjectorNext",
        "YM.MultiNext", "YM.WilsonBulk", "YM.Bid", "YM.PCalc", "YM.Dash", "YM.Org", "YM.ProofPorts", "YM.Pressure",
        "YM.Ac", "YM.Corona", "YM.Overlay", "YM.Branch", "YM.Extension", "YM.PREC", "YM.Spark",
        "YM.Frontier6", "YM.Shoot", "YM.Ovens", "YM.Wallet"],
    "S2b run selection and assembly of the final witness": ["YM.Integration", "YM.R2I", "YM.RG17"],
    "S3 limits: fixed-volume UV limit, full/infinite volume, extraction": ["YM.Extraction", "YM.FullVolume",
        "YM.Slice", "YM.Distribution"],
    "S4 OS structure, phases, reconstruction (Wightman)": ["YM.OS", "YM.Phase", "YM.Ground", "YM.EveryPhase",
        "YM.Boundary", "YM.Fields", "YM.Mink", "YM.Spin", "YM.Spectral", "YM.Hilbert", "YM.SNAG",
        "YM.TimeKernel"],
    "W shared work packages and analysis utilities": ["YM.Work", "YM.Analysis", "YM.Laurent", "YM.Complex",
        "YM.Analytic", "YM.LocalH", "YM.Vac", "YM.Heat", "YM.Paley"],
    "S5 stress tensor, Ward identities, trace law": ["YM.Ward", "YM.Trace", "YM.Trace2", "YM.TraceExtension",
        "YM.Maxwell"],
    "S6 OPE and contact extensions": ["YM.OPE", "YM.Contacts", "YM.MultipleContact", "YM.Contact"],
    "S7 perturbative comparison, running coupling": ["YM.Pert", "YM.PertExtension", "YM.SharpGram", "YM.Climb"],
}
d2s = {d: s for s, ds in STAGES.items() for d in ds}
rows = list(csv.DictReader(open(os.path.join(graph, "solution_closure_by_dir.tsv")), delimiter="\t"))
reach = {}
if audit and os.path.exists(os.path.join(audit, "by-topdir.tsv")):
    for r in csv.DictReader(open(os.path.join(audit, "by-topdir.tsv")), delimiter="\t"):
        reach[r["topdir"]] = (int(r["declarations"]), int(r["reached_from_jointExistence"]), int(r["reached_from_17"]))
agg, unassigned = {}, []
for r in rows:
    s = d2s.get(r["dir"])
    if s is None:
        unassigned.append(r["dir"]); s = "S? unassigned"
    a = agg.setdefault(s, [0, 0, 0, 0, 0, []])
    a[0] += int(r["modules"]); a[1] += int(r["lines"])
    t, x, y = reach.get(r["dir"], (0, 0, 0))
    a[2] += t; a[3] += x; a[4] += y; a[5].append(r["dir"])
print("stage\tmodules\tlines\tdecls\treached_jE\treached_17")
for s in sorted(agg):
    m, l, t, x, y, _ = agg[s]
    print(f"{s}\t{m}\t{l}\t{t}\t{x}\t{y}")
print("unassigned dirs:", unassigned)
