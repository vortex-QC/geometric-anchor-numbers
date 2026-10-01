# geometric-anchor-numbers

Replication package. Paper DOI: [10.5281/zenodo.23084693](https://doi.org/10.5281/zenodo.23084693) (backfilled after publish).

**File ↔ section map**

| Lean file | Paper section |
|---|---|
| GeoAnchorPi1.lean | §3.1 lattice pi1 = Z (36 groups) |
| GeoAnchorNumCollapse.lean | §3.2 cardinality asymmetry |
| GeoAnchorSimple.lean | §3.3 8-vs-7 statement piece |
| GeoAnchorLattice.lean | §3.3 collapse lattice T1–T5 |
| GeoAnchorCollapse.lean / GeoAnchorIdentity.lean | supporting pieces |

**Replication**: `cd lean && lake build` (toolchain pinned v4.33.1). `replication/` holds the enumeration/simulation results (A'4 commitment axis, isometry grading, BKT flow). Companion paper: The Constructive Calculus of Anchors (DOI 10.5281/zenodo.23084467).

## License

Code (`lean/`): MIT. Docs: CC-BY-4.0.
