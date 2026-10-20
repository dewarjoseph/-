"""
src/chair44/__init__.py
================================================================================
3D Chair44 (Q/R^44) Aperiodic Field Theory Package.
================================================================================
"""

from src.chair44.geometry import (
    U3,
    BASE_CENTERS,
    get_chair_cubes,
    get_chair_faces,
    perm_mat,
    generate_supertile_tiles,
    build_tile_adjacency,
)

from src.chair44.frames import (
    FR30,
    ACHIRAL,
    CANONICAL_HOMO,
    compute_fr30_poses,
    get_valid_contact_pairs,
    verify_kamenetsky_theorems,
)

from src.chair44.clifford import (
    SIGMA,
    q8_element_label,
    quaternion_trace,
    compute_clifford_holonomy,
    build_clifford_hamiltonian,
    analyze_clifford_q8_connection,
)

from src.chair44.laplacians import (
    build_soldered_laplacian,
    analyze_soldered_laplacian,
    build_level1_tile_laplacian,
    compute_exact_level1_eigenvalues,
    compute_level1_tile_laplacian,
)

from src.chair44.cellular_complex import (
    build_polyhedral_chair_complex,
    build_boundary_operators,
    compute_hodge_laplacians,
    verify_caging,
)

from src.chair44.periodic_crystal import (
    homomorphic_map,
    get_lambda7_basis,
    generate_lambda7_periodic_chairs,
    generate_rotated_cell_periodic,
)

__all__ = [
    "U3",
    "BASE_CENTERS",
    "get_chair_cubes",
    "get_chair_faces",
    "perm_mat",
    "generate_supertile_tiles",
    "build_tile_adjacency",
    "FR30",
    "ACHIRAL",
    "CANONICAL_HOMO",
    "compute_fr30_poses",
    "get_valid_contact_pairs",
    "verify_kamenetsky_theorems",
    "SIGMA",
    "q8_element_label",
    "quaternion_trace",
    "compute_clifford_holonomy",
    "build_clifford_hamiltonian",
    "analyze_clifford_q8_connection",
    "build_soldered_laplacian",
    "analyze_soldered_laplacian",
    "build_level1_tile_laplacian",
    "compute_exact_level1_eigenvalues",
    "compute_level1_tile_laplacian",
    "build_polyhedral_chair_complex",
    "build_boundary_operators",
    "compute_hodge_laplacians",
    "verify_caging",
    "homomorphic_map",
    "get_lambda7_basis",
    "generate_lambda7_periodic_chairs",
    "generate_rotated_cell_periodic",
]
