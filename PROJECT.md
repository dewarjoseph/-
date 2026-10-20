# Project: Quasicrystal Chair44 & 6D->3D Chiral Icosahedral Quasicrystal Program

## Architecture
- **Clean Modular Repository Layout**:
  - `src/chair44/`: 3D/4D Chair44 geometry, FR30 language, Clifford $Q_8$ holonomy, soldered & Hodge Laplacians, $\Lambda_7$ periodic crystal.
  - `src/icosahedral_qc/`: 6D->3D projection geometry ($P_\parallel, P_\perp$), acceptance windows ($W_b, -W_b, W_a$), lattice BFS, structure factor, vibrational circular dichroism, Weyl continuum integration, quantum metric, non-Hermitian skin effect, Floquet-phason electrodynamics.
  - `src/cross_disciplinary/`: Wigner-Smith transient scaling, 4D tesseract chair holonomy, viral quasicrystallography (PDB 1STM), DNA brick & chromatin caging, chiral photonic sensing, epigraphic grammar, and bibliometric synthesis.
  - `benchmarks/`: Standalone deterministic benchmark scripts for Modules 1-35 (`module1_...py` through `module35_...py`).
  - `data/`: Deterministic JSON output ledgers and experimental datasets.
  - `figures/`: Publication-quality vector figures (`.pdf`, `.png`) generated directly from benchmark data.
  - `paper/`: Complete LaTeX monograph (`paper/main.tex`, `paper/references.bib`) compiled to `paper/main.pdf` via Tectonic.
  - `tests/`: Automated test suite (`tests/verify_all.py`, `tests/test_chair44.py`, `tests/test_qc.py`, `tests/test_errata.py`).
  - `docs/`: Reference manuscripts and documentation.

## Feature Inventory
| # | Feature | Description | Milestone | Source |
|---|---------|-------------|-----------|--------|
| 1 | Repository Restructuring | Clean modular directory tree and Python package architecture | M1 | R1 |
| 2 | Chair44 Core Library | `src/chair44/` implementing geometry, FR30 language, Q8 holonomy, soldered Laplacians, Hodge caging | M1 | R1 |
| 3 | 6D->3D Quasicrystal Core | `src/icosahedral_qc/` implementing projectors, windows, BFS, structure factor, Weyl limits, QGT, HONHSE, Floquet | M1 | R1 |
| 4 | Legacy Benchmarks R1-M27 | Unify and reconstruct historical benchmarks reproducing all published data tables | M1 | R1 |
| 5 | Erratum 1: P_perp Row 2 | Restore omitted $+\tau$ in Row 2 Col 4; verify all 4 projector identities to $< 2.3 \times 10^{-16}$ | M1 | R4.1 |
| 6 | Erratum 2: Table 3 Exponent | Reconcile $\eta=0.25$ sum residual to $-1.0130 \times 10^{-5}$ correcting $10^{-3}$ typo | M1 | R4.2 |
| 7 | Erratum 3: Quadrature Ratio | Clarify unrounded 16-point Gauss-Legendre quadrature ratio $0.8713$ vs rounded $0.8710$ | M1 | R4.3 |
| 8 | Erratum 4: Scaling Dictionary | Formulate physical unit dictionary across photonic, biomolecular, and cosmological regimes | M1 | R4.4 |
| 9 | M28 Mode-Resolved IPR | Compute IPR across codimension-2 hinges, codimension-1 faces, and interior bulk | M2 | R2.1 |
| 10 | M28 Solenoidal Torque Pinning | Solenoidal circulating currents and optical/acoustic angular momentum pinning at hinges | M2 | R2.2 |
| 11 | M28 3D Torus Winding Topology | Compute $\mathbb{T}^3$ joint momentum-phason point-gap winding numbers and EP immunity audit | M2 | R2.3 |
| 12 | M28 Dual-Control Parity Audit | Verify exact mirror odd parity on $-W_b$ and control zero on $W_a$ across all M28 observables | M2 | R2.4 |
| 13 | Pillar 1: Wigner-Smith (M29) | Large patch $R \ge 18-20$, $Q_{WS}(\omega)$ group-delay splitting, FRB transients, $C_\ell^{\alpha\alpha} \propto \ell^{-2}$ | M3 | R3.1 |
| 14 | Pillar 2: 4D Tesseract Chair (M30) | Multi-core search for $C_4$ frame assignments, boundary 3-face pruning to FR30, $Spin(4)$ holonomy | M3 | R3.2 |
| 15 | Pillar 3: Viral Quasicrystal (M31) | Real PDB 1STM coordinates, $\chi_b$, $\mathcal{D}_{Lap}$, $g_{xy}$, HONHSE at pentamers, Mol* sidecar viewer | M3 | R3.3 |
| 16 | Pillar 4: 2-Adic DNA & Chromatin (M32) | DNA brick self-assembly model, ENCODE cCREs, JASPAR CTCF, UCSC phyloP, Hodge caging | M3 | R3.4 |
| 17 | Pillar 5: Chiral Photonic Sensing (M33) | $C_{opt}$ at 6.74x HONHSE hotspots, PubChem/ChEMBL enantiomers, STRING/Reactome networks | M3 | R3.5 |
| 18 | Pillar 6: Epigraphy & Grammar (M34) | Contact grammar $|P_0|=30 \to |P^*|=44$, 135 facet triples, entropy superconvergence, sequence restoration | M3 | R3.6 |
| 19 | Pillar 7: Bibliometric Synthesis (M35) | Systematic queries across arXiv, OpenAlex, EuropePMC, PubMed; DOI/URL citations | M3 | R3.7 |
| 20 | Monograph Authoring | Complete publication-grade LaTeX monograph (`paper/main.tex`) with 14 sections and 3 appendices | M4 | R5 |
| 21 | Figure Generation Pipeline | Generate publication-quality figures (`figures/*.pdf`) directly from benchmark data | M4 | R5 |
| 22 | Tectonic PDF Compilation | Compile `paper/main.tex` into `paper/main.pdf` (35+ pages, zero fatal errors, zero `??` refs) | M4 | R5 |
| 23 | Automated E2E Verification Suite | `tests/verify_all.py` testing 100% of mathematical and scientific assertions across Tiers 1–4 | E2E / M5 | AC |
| 24 | Git Clean State & Victory Report | Clean repository commits, zero untracked artifacts, victory report to Sentinel | M5 | AC |

## Milestones
| # | Name | Scope | Dependencies | Status |
|---|------|-------|-------------|--------|
| M1 | Core Library Reconstruction & Legacy Benchmarks | `src/chair44/`, `src/icosahedral_qc/`, legacy benchmarks R1-M27, errata R4 reconciliation | none | PLANNED |
| M2 | Module 28 Execution | `benchmarks/module28_honhse_ipr_3d_winding_benchmark.py`, IPR, torque pinning, $\mathbb{T}^3$ torus winding, dual-control parity | M1 | PLANNED |
| M3 | 5x Cross-Disciplinary Frontier Program | `src/cross_disciplinary/`, benchmarks M29–M35 across 7 Science pillars, real datasets (1STM, PubChem, ENCODE, arXiv) | M1 | PLANNED |
| M4 | Monograph Authoring & Figure Pipeline | `paper/main.tex`, `figures/*.pdf`, compilation via Tectonic to `paper/main.pdf` (35+ pages) | M1, M2, M3 | PLANNED |
| M5 | Final E2E Test Suite Pass & Adversarial Hardening | Phase 1: 100% pass on E2E test suite (Tiers 1–4); Phase 2: Tier 5 adversarial hardening | M1, M2, M3, M4, TEST_READY | PLANNED |

## Parallel Track: E2E Testing Track
- **Owner**: E2E Testing Orchestrator
- **Scope**: Requirement-driven, opaque-box test architecture (`TEST_INFRA.md`), generating test suites across Tiers 1–4, culminating in `TEST_READY.md`.

## Interface Contracts
### `src/chair44` ↔ `benchmarks` / `tests`
- `geometry.py`: `get_chair_cubes() -> np.ndarray (7, 3)`, `get_chair_faces() -> List[Face]`.
- `frames.py`: `compute_fr30_poses(k: int) -> Set[Pose]`, `get_valid_contact_pairs() -> List[Tuple]`.
- `clifford.py`: `compute_clifford_holonomy(cycle: List) -> np.ndarray (2, 2)`, `quaternion_trace(Q) -> float`.
- `laplacians.py`: `build_soldered_laplacian(...) -> np.ndarray`, `compute_exact_level1_eigenvalues() -> Tuple`.
- `cellular_complex.py`: `build_boundary_operators(...) -> (d0, d1, d2)`, `verify_caging() -> bool`.
- `periodic_crystal.py`: `homomorphic_map(x, y, z) -> int`, `get_lambda7_basis() -> np.ndarray (3, 3)`.

### `src/icosahedral_qc` ↔ `benchmarks` / `tests`
- `projectors.py`: `get_projectors() -> Tuple[np.ndarray, np.ndarray]` ($P_\parallel, P_\perp \in \mathbb{R}^{3 \times 6}$ with restored $+\tau$).
- `windows.py`: `get_acceptance_window(name: str) -> ConvexHull` (supports `'W_b'`, `'-W_b'`, `'W_a'`).
- `lattice_bfs.py`: `generate_quasicrystal_patch(radius: float, window_name: str) -> np.ndarray (N, 3)`.
- `weyl_continuum.py`: `compute_analytical_infinity_limits(hull: ConvexHull, n_gl: int = 16) -> Dict`.
- `structure_factor.py`: `compute_bragg_bispectrum(points: np.ndarray, q_triples: List) -> complex`.
- `quantum_metric.py`: `compute_fubini_study_metric(...) -> np.ndarray (3, 3)`.
- `non_hermitian.py`: `compute_non_hermitian_skin_modes(points: np.ndarray, eta: float) -> Tuple`.
- `floquet_phason.py`: `compute_floquet_dichroism(omega: float, phi_dot: float) -> float`.

### `src/cross_disciplinary` ↔ `benchmarks` / `paper`
- `wigner_smith.py`: `compute_wigner_smith_delay(patch: np.ndarray, freq_range: np.ndarray) -> np.ndarray`.
- `tesseract_chair.py`: `search_4d_chair_frames(max_workers: int = 24) -> Dict`.
- `viral_quasicrystal.py`: `analyze_viral_capsid(cif_path: str) -> Dict` ($\chi_b, \mathcal{D}_{Lap}, g_{xy}$, Mol* annotations).
- `chromatin_caging.py`: `model_dna_brick_assembly() -> Dict`, `evaluate_genomic_caging() -> Dict`.
- `chiral_sensing.py`: `compute_optical_chirality_density(field: np.ndarray) -> np.ndarray`.
- `epigraphic_grammar.py`: `evaluate_contact_grammar_entropy() -> Dict`.
- `bibliometrics.py`: `synthesize_scholarly_metadata() -> Dict`.

## Code Layout
- `src/chair44/`: Pure Python modules with type annotations and docstrings.
- `src/icosahedral_qc/`: Pure Python + NumPy/SciPy modules.
- `src/cross_disciplinary/`: Frontier modules utilizing Science plugins and 24-core parallelism.
- `benchmarks/`: Self-contained runnable scripts outputting deterministic results to `data/`.
- `data/`: JSON summaries and numerical arrays.
- `figures/`: Vector PDF and high-res PNG plots.
- `paper/`: Complete LaTeX source (`main.tex`, `references.bib`, macros) and `main.pdf`.
- `tests/`: Automated test suite with `verify_all.py` root runner.
