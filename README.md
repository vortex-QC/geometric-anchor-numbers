# geometric-anchor-numbers

Replication package. Paper DOI: [10.5281/zenodo.23104139](https://doi.org/10.5281/zenodo.23104139) (v1.2, version chain concept 10.5281/zenodo.23084692; v1.1 = 10.5281/zenodo.23086696, v1.0 = 10.5281/zenodo.23084693).

**File ↔ section map**

| Lean file | Paper section |
|---|---|
| GeoAnchorPi1.lean | §3.1 lattice pi1 = Z (36 groups) |
| GeoAnchorNumCollapse.lean | §3.2 cardinality asymmetry |
| GeoAnchorSimple.lean | §3.3 8-vs-7 statement piece |
| GeoAnchorLattice.lean | §3.3 collapse lattice T1–T5 |
| GeoAnchorCorridor.lean | §3.3/§6 corridor theorem, lattice first layer (mod-2 reading; 14 theorem-level pieces, zero sorry; added 2026-10-02) |
| GeoAnchorCollapse.lean / GeoAnchorIdentity.lean | supporting pieces |

**Replication**: `cd lean && lake build` (toolchain pinned v4.33.1). `replication/` holds the enumeration/simulation results (A'4 commitment axis, isometry grading, BKT flow; v1.1 §6 configuration genetics: constraint-order round + open-universe round; v1.2 §6.5: global open-universe extension round — 58,762 chains, two-order experiment, seven preregistered criteria OX-0–OX-6 — preregistered script and results included). Companion paper: The Constructive Calculus of Anchors (DOI 10.5281/zenodo.23086699).

## License

Code (`lean/`): MIT. Docs: CC-BY-4.0.
