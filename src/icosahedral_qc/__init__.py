"""
src/icosahedral_qc/__init__.py
================================================================================
6D -> 3D Chiral Icosahedral Cut-and-Project Quasicrystal Package.
================================================================================
"""

from src.icosahedral_qc.projectors import (
    TAU,
    NORM,
    V_PAR,
    V_PERP,
    P_PAR,
    P_PERP,
    PI_PAR,
    PI_PERP,
    get_projectors,
    verify_projection_orthogonality,
    verify_projector_algebra,
    compute_icosahedral_symmetry_groups,
    PHYSICAL_SCALING_DICTIONARY,
)

from src.icosahedral_qc.windows import (
    P0_CHIRAL,
    get_acceptance_windows,
    get_acceptance_window,
    build_acceptance_windows,
)

from src.icosahedral_qc.lattice_bfs import (
    bfs_vectorized_6d,
    generate_quasicrystal_patch,
    build_patch_adjacency,
)

from src.icosahedral_qc.structure_factor import (
    M_LIST,
    K_PAR,
    K_PERP,
    TRIPLETS,
    get_wavevector_module,
    compute_structure_factor,
    compute_bragg_bispectrum,
    evaluate_bispectrum,
)

from src.icosahedral_qc.laplacian_dichroism import (
    D_ALPHA_PAR,
    FACTOR_K,
    evaluate_patch_observables,
    compute_laplacian_dichroism,
)

from src.icosahedral_qc.weyl_continuum import (
    integrate_polyhedron_exp,
    compute_analytical_infinity_limits,
)

from src.icosahedral_qc.quantum_metric import (
    compute_fubini_study_metric,
    compute_quantum_metric_tensor,
    verify_quantum_metric_parity,
)

from src.icosahedral_qc.non_hermitian import (
    classify_spatial_regions,
    build_non_hermitian_hamiltonian,
    compute_non_hermitian_skin_modes,
    compute_non_bloch_gbz_decay,
)

from src.icosahedral_qc.floquet_phason import (
    compute_floquet_dichroism,
    compute_phason_spectral_loop,
    compute_persistent_edge_current,
)

__all__ = [
    "TAU",
    "NORM",
    "V_PAR",
    "V_PERP",
    "P_PAR",
    "P_PERP",
    "PI_PAR",
    "PI_PERP",
    "get_projectors",
    "verify_projection_orthogonality",
    "verify_projector_algebra",
    "compute_icosahedral_symmetry_groups",
    "PHYSICAL_SCALING_DICTIONARY",
    "P0_CHIRAL",
    "get_acceptance_windows",
    "get_acceptance_window",
    "build_acceptance_windows",
    "bfs_vectorized_6d",
    "generate_quasicrystal_patch",
    "build_patch_adjacency",
    "M_LIST",
    "K_PAR",
    "K_PERP",
    "TRIPLETS",
    "get_wavevector_module",
    "compute_structure_factor",
    "compute_bragg_bispectrum",
    "evaluate_bispectrum",
    "D_ALPHA_PAR",
    "FACTOR_K",
    "evaluate_patch_observables",
    "compute_laplacian_dichroism",
    "integrate_polyhedron_exp",
    "compute_analytical_infinity_limits",
    "compute_fubini_study_metric",
    "compute_quantum_metric_tensor",
    "verify_quantum_metric_parity",
    "classify_spatial_regions",
    "build_non_hermitian_hamiltonian",
    "compute_non_hermitian_skin_modes",
    "compute_non_bloch_gbz_decay",
    "compute_floquet_dichroism",
    "compute_phason_spectral_loop",
    "compute_persistent_edge_current",
]
