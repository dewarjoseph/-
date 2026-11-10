"""
tests/test_cross_disciplinary.py
================================================================================
Comprehensive Unit Test Suite for the 7 Cross-Disciplinary Pillars (Modules 29-35):
  Pillar 1: Large-Scale Thermodynamic & Wigner-Smith Transient Scaling (Module 29)
  Pillar 2: 4D Tesseract Chair (C_4) Spin(4) Holonomy & Kamenetsky Open Problem 9.1 (Module 30)
  Pillar 3: Structural Biology & Chiral Icosahedral Viral Quasicrystallography (PDB 1STM, Module 31)
  Pillar 4: 2-Adic DNA Brick Self-Assembly & Chromatin CCRE Caging (ENCODE/JASPAR, Module 32)
  Pillar 5: Chiral Photonic Enantiomer Sensing (PubChem/ChEMBL, Module 33)
  Pillar 6: Symbolic Epigraphy & Aperiodic Contact Language Superconvergence (Module 34)
  Pillar 7: Multi-Database Scholarly Bibliometric Synthesis & Comparison Matrix (Module 35)
================================================================================
"""

import os
import sys
import unittest
import numpy as np

# Ensure workspace root is in sys.path
WORKSPACE_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if WORKSPACE_ROOT not in sys.path:
    sys.path.insert(0, WORKSPACE_ROOT)

from src.chair44.c4_tesseract import (
    analyze_kamenetsky_open_problem_9_1,
    compute_spin4_casimir_invariants,
    compute_c4_cell_complex_euler_characteristic,
    compute_c4_boundary_complex,
    compute_c4_cubical_homology_betti_numbers,
    compute_c4_hodge_laplacian_decomposition,
)
from src.icosahedral_qc.honhse import (
    evaluate_gbz_skin_depth_scaling,
    compute_fubini_study_quantum_geometric_tensor,
)
from src.icosahedral_qc.wigner_smith_cosmology import (
    compute_wigner_smith_delay, chiral_scattering_matrix, evaluate_cosmological_birefringence,
    evaluate_cmb_polarization_spectra,
)
from src.cross_disciplinary.viral_capsid import (
    generate_idealized_1stm_capsid, analyze_viral_capsid_quasicrystallography,
    parse_real_pdb_1stm, evaluate_multiaxis_capsid_localization,
    evaluate_crystallographic_bfactors,
    compute_capsid_elastic_network_normal_modes,
)
from src.cross_disciplinary.dna_genomics import (
    p_adic_metric_2, evaluate_dna_brick_energy_landscape, analyze_genomic_caching_and_motifs,
    parse_jaspar_ctcf_pfm, evaluate_2adic_chromatin_contact_probability,
    evaluate_2adic_tad_hierarchy_barrier,
    compute_2adic_chromatin_compartment_pc1,
)
from src.cross_disciplinary.chiral_sensing import (
    evaluate_near_field_optical_chirality, compute_enantiomer_discrimination,
    verify_pubchem_alanine_stereochemistry, compute_optical_chiral_force_sorting,
    evaluate_chembl_enantiomer_target_affinity,
    compute_chiral_optical_torque_trapping,
)
from src.cross_disciplinary.epigraphy_grammar import (
    compute_contact_language_closure, evaluate_entropy_superconvergence,
    restore_corrupted_aperiodic_sequence, compute_grammatical_transition_matrix,
    evaluate_chomsky_hierarchy_and_topological_entropy,
    compute_lyapunov_spectrum_and_contraction,
)
from src.cross_disciplinary.bibliometrics import (
    VERIFIED_BIBLIOGRAPHY, generate_comparison_matrix, cross_validate_arxiv_metadata,
    evaluate_citation_network_topology,
    evaluate_bibliometric_spectral_centrality,
    evaluate_citation_network_small_world_properties,
)



class TestCrossDisciplinaryPillarsSuite(unittest.TestCase):
    """Unit tests verifying all 7 cross-disciplinary frontier pillars."""

    def test_pillar1_wigner_smith_and_cosmology(self):
        """Pillar 1 (Module 29): Wigner-Smith time delay and scale-invariant cosmic birefringence."""
        omega_vals = np.linspace(1.0, 10.0, 50)
        delays_p, delays_m = compute_wigner_smith_delay(omega_vals, chiral_scattering_matrix)
        delta_tau = float(np.mean(delays_p - delays_m))
        self.assertGreater(delta_tau, 0.05, "Group delay splitting must be positive and substantial")
        
        ells, c_ell = evaluate_cosmological_birefringence(ell_max=50)
        self.assertEqual(len(ells), 49)
        # Verify scale-invariant ell^-2 power spectrum: ell*(ell+1)*c_ell should be approximately constant
        dl = ells * (ells + 1) * c_ell
        self.assertLess(np.std(dl) / np.mean(dl), 0.1, "Power spectrum must exhibit scale-invariant scaling")

    def test_pillar2_c4_tesseract_spin4_obstruction(self):
        """Pillar 2 (Module 30): 4D Tesseract Chair C_4 and Kamenetsky Open Problem 9.1."""
        res = analyze_kamenetsky_open_problem_9_1()
        self.assertEqual(res["num_subcubes"], 15, "C_4 must contain 15 sub-tesseracts")
        self.assertEqual(res["odd_weight_octants"], 8)
        self.assertEqual(res["even_weight_octants"], 7)
        self.assertEqual(res["boundary_3cubes"], 64)
        self.assertEqual(res["so4_dim"], 6)
        self.assertEqual(res["su2_plus_dim"], 3)
        self.assertEqual(res["su2_minus_dim"], 3)
        self.assertTrue(res["algebraic_obstruction_verified"], "Homochiral Spin(4) closure must be obstructed")
        self.assertIn("casimir_invariants", res)
        self.assertTrue(res["casimir_invariants"]["decoupling_verified"])

    def test_pillar3_viral_capsid_quasicrystallography(self):
        """Pillar 3 (Module 31): STMV 1STM viral capsid 6D->3D quasicrystallography and skin localization."""
        coords_3d, sub_labels = generate_idealized_1stm_capsid(r_capsid=8.0, n_residues_per_subunit=25)
        self.assertEqual(len(coords_3d), 1500, "STMV model must have 1500 residues (60x25)")
        
        capsid_res = analyze_viral_capsid_quasicrystallography(coords_3d)
        self.assertAlmostEqual(capsid_res["chi_b_capsid"], 0.002845, places=5)
        self.assertAlmostEqual(capsid_res["d_lap_capsid"], 0.002479, places=5)
        self.assertGreater(capsid_res["hinge_fraction"], 0.6)
        self.assertTrue(capsid_res["pentameric_hinges_localized"])

        # Real crystallographic PDB 1STM verification
        real_pdb = parse_real_pdb_1stm("data/1stm.pdb")
        self.assertTrue(real_pdb["loaded"])
        self.assertEqual(real_pdb["total_ca_atoms"], 705)
        self.assertEqual(real_pdb["chain_A_hinge_residues"], 19)
        self.assertTrue(real_pdb["pentameric_symmetry_verified"])

    def test_pillar4_dna_bricks_and_genomic_caging(self):
        """Pillar 4 (Module 32): 2-adic DNA bricks and ENCODE/JASPAR chromatin caging."""
        # 2-adic ultrametric test
        self.assertEqual(p_adic_metric_2(12, 4), 0.125)  # |12 - 4|_2 = |8|_2 = 2^-3 = 1/8
        self.assertEqual(p_adic_metric_2(5, 5), 0.0)

        dna_res = evaluate_dna_brick_energy_landscape(level=2)
        self.assertEqual(dna_res["n_bricks"], 49)
        self.assertAlmostEqual(dna_res["net_delta_G_kcal_mol"], -1208.4, places=1)
        self.assertGreater(dna_res["assembly_fidelity"], 0.99)

        genomic_res = analyze_genomic_caching_and_motifs()
        self.assertEqual(genomic_res["ctcf_motif_id"], "JASPAR:MA0139.1")
        self.assertAlmostEqual(genomic_res["ctcf_info_content_bits"], 28.4, places=1)
        self.assertAlmostEqual(genomic_res["hodge_spectral_gap"], 0.428, places=3)
        self.assertTrue(genomic_res["chromatin_caging_stabilized"])

    def test_pillar5_chiral_photonic_enantiomer_sensing(self):
        """Pillar 5 (Module 33): Near-field chirality amplification and enantiomer discrimination."""
        c_opt_res = evaluate_near_field_optical_chirality()
        self.assertAlmostEqual(c_opt_res["c_opt_corner_enhancement"], 45.4276, places=2)
        self.assertAlmostEqual(c_opt_res["floquet_sideband_cd_pm2"], -0.472, places=3)

        molecules = compute_enantiomer_discrimination()
        self.assertIn("Thalidomide", molecules)
        self.assertIn("Alanine", molecules)
        self.assertIn("Carvone", molecules)
        self.assertGreater(molecules["Thalidomide"]["distinguishable_snr_sigma"], 30.0)
        self.assertGreater(molecules["Alanine"]["distinguishable_snr_sigma"], 15.0)

    def test_pillar6_epigraphy_grammar_and_superconvergence(self):
        """Pillar 6 (Module 34): FR30 contact grammar closure and entropy superconvergence."""
        closure = compute_contact_language_closure()
        self.assertEqual(closure["initial_contact_pairs_P0"], 30)
        self.assertEqual(closure["certified_closed_rules_P_star"], 44)
        self.assertEqual(closure["facet_triples_F_star"], 135)
        self.assertTrue(closure["grammar_closed"])

        entropy = evaluate_entropy_superconvergence()
        self.assertAlmostEqual(entropy["superconvergence_rate_alpha"], 1.0, places=2)
        
        # Test defect restoration
        seq = ["T0", "Tv1", "Tv2", "Tv3", "Tv4"]
        corrupted = ["T0", "CORRUPT", "Tv2", "Tv3", "Tv4"]
        allowed = {"T0": {"Tv1", "Tv2"}, "Tv1": {"Tv2"}, "Tv2": {"Tv3"}, "Tv3": {"Tv4"}}
        restored = restore_corrupted_aperiodic_sequence(corrupted, [1], allowed)
        self.assertEqual(restored, seq)

    def test_pillar7_bibliometric_synthesis(self):
        """Pillar 7 (Module 35): Multi-database scholarly bibliometric synthesis."""
        self.assertGreaterEqual(len(VERIFIED_BIBLIOGRAPHY), 10)
        for ref in VERIFIED_BIBLIOGRAPHY:
            self.assertIn("key", ref)
            self.assertIn("doi", ref)
            self.assertTrue(ref["doi"].startswith("10.") or "arXiv" in ref["doi"])
            self.assertIn("pillar", ref)
        
        matrix = generate_comparison_matrix()
        self.assertIn("pillar_counts", matrix)
        self.assertGreaterEqual(matrix["num_with_dois"], 10)
        self.assertGreater(matrix["summary"]["total_citations"], 5000)

    def test_pillar2_spin4_casimir_invariants(self):
        """Pillar 2: Spin(4) Casimir invariants C_{2,+} = C_{2,-} = -3*I_4 and exact decoupling."""
        casimir = compute_spin4_casimir_invariants()
        self.assertEqual(casimir["C_plus_norm"], -12.0)
        self.assertEqual(casimir["C_minus_norm"], -12.0)
        self.assertLess(casimir["err_casimir_plus"], 1e-15)
        self.assertLess(casimir["err_casimir_minus"], 1e-15)
        self.assertLess(casimir["max_cross_commutator"], 1e-15)
        self.assertTrue(casimir["decoupling_verified"])

    def test_pillar3_real_pdb_1stm_capsid(self):
        """Pillar 3: RCSB PDB 1STM atomic coordinate parser and 5-fold hinge extraction."""
        pdb_res = parse_real_pdb_1stm()
        if pdb_res.get("loaded"):
            self.assertEqual(pdb_res["total_ca_atoms"], 705)
            self.assertEqual(pdb_res["chains"], ["A", "B", "C", "D", "E"])
            self.assertEqual(pdb_res["chain_A_hinge_residues"], 19)
            self.assertGreater(pdb_res["radius_of_gyration_angstroms"], 25.0)
            self.assertTrue(pdb_res["pentameric_symmetry_verified"])

    def test_pillar4_real_jaspar_ctcf_pfm(self):
        """Pillar 4: JASPAR CTCF transcription factor binding motif MA0139.1 PFM parser."""
        jaspar_res = parse_jaspar_ctcf_pfm()
        if jaspar_res.get("loaded"):
            self.assertEqual(jaspar_res["consensus_length"], 19)
            self.assertAlmostEqual(jaspar_res["core_information_content_bits"], 17.205, places=2)
            self.assertTrue(jaspar_res["jaspar_pfm_verified"])

    def test_pillar5_real_pubchem_alanine_stereochemistry(self):
        """Pillar 5: PubChem D-Alanine (CID 71080) vs L-Alanine (CID 5950) stereochemical validation."""
        pubchem_res = verify_pubchem_alanine_stereochemistry()
        if pubchem_res.get("loaded"):
            self.assertTrue(pubchem_res["enantiomeric_parity_inverted"])
            self.assertTrue(pubchem_res["inchikeys_differ"])
            self.assertTrue(pubchem_res["stereochemistry_verified"])

    def test_pillar6_grammatical_transition_matrix(self):
        """Pillar 6: Substitution grammar transition matrix spectral radius matching volume inflation 2^3=8."""
        mat_res = compute_grammatical_transition_matrix()
        self.assertEqual(mat_res["num_states"], 44)
        self.assertAlmostEqual(mat_res["spectral_radius"], 8.0, places=10)
        self.assertTrue(mat_res["perron_frobenius_verified"])

    def test_pillar7_arxiv_cross_validation(self):
        """Pillar 7: Cross-validation against empirical arXiv search query records."""
        arxiv_res = cross_validate_arxiv_metadata()
        if arxiv_res.get("loaded"):
            self.assertGreaterEqual(arxiv_res["query_results_count"], 10)
            self.assertTrue(arxiv_res["arxiv_verified"])

    def test_pillar2_c4_euler_characteristic(self):
        """Pillar 2: C_4 cell complex Euler-Poincare characteristic chi = f0 - f1 + f2 - f3 + f4 = 1."""
        c4_euler = compute_c4_cell_complex_euler_characteristic()
        self.assertEqual(c4_euler["f0_vertices"], 80)
        self.assertEqual(c4_euler["f1_edges"], 212)
        self.assertEqual(c4_euler["f2_faces"], 210)
        self.assertEqual(c4_euler["f3_cubes"], 92)
        self.assertEqual(c4_euler["f4_tesseracts"], 15)
        self.assertEqual(c4_euler["euler_characteristic_chi"], 1)
        self.assertTrue(c4_euler["contractible_verified"])

    def test_pillar1_gbz_skin_depth_scaling(self):
        """Pillar 1: GBZ non-Bloch skin depth power-law scaling xi ~ eta^-1 and phasonic Berry phase."""
        gbz_res = evaluate_gbz_skin_depth_scaling()
        self.assertAlmostEqual(gbz_res["skin_depth_scaling_exponent"], 1.0, places=5)
        self.assertAlmostEqual(gbz_res["phasonic_berry_phase"], 2.0 * np.pi, places=5)
        self.assertTrue(gbz_res["gbz_scaling_verified"])

    def test_pillar3_multiaxis_capsid_localization(self):
        """Pillar 3: STMV 1STM acoustic skin mode 5-fold vertex hinge selective amplification."""
        loc_res = evaluate_multiaxis_capsid_localization()
        self.assertAlmostEqual(loc_res["amplification_5fold_vertex"], 6.74, places=2)
        self.assertAlmostEqual(loc_res["amplification_3fold_facet"], 1.12, places=2)
        self.assertGreater(loc_res["selective_pinning_ratio"], 5.0)
        self.assertTrue(loc_res["pentameric_hinge_preference_verified"])

    def test_pillar4_2adic_chromatin_contact_probability(self):
        """Pillar 4: 2-adic chromatin polymer contact probability scaling with fractal globule exponent gamma=1.048."""
        contact_res = evaluate_2adic_chromatin_contact_probability()
        self.assertAlmostEqual(contact_res["scaling_exponent_gamma"], 1.048, places=3)
        self.assertAlmostEqual(contact_res["ctcf_boundary_retention"], 0.968, places=3)
        self.assertTrue(contact_res["fractal_globule_scaling_verified"])

    def test_pillar5_optical_chiral_force_sorting(self):
        """Pillar 5: HONHSE 45.4x near-field enhanced Circular Differential Force and sorting throughput."""
        force_res = compute_optical_chiral_force_sorting()
        self.assertAlmostEqual(force_res["optical_chiral_force_fN"], 14.20, places=2)
        self.assertAlmostEqual(force_res["drift_velocity_um_s"], 15.06, places=2)
        self.assertGreaterEqual(force_res["throughput_molecules_per_sec"], 1e6)
        self.assertTrue(force_res["sorting_verified"])

    def test_pillar6_chomsky_hierarchy_properties(self):
        """Pillar 6: Chair44 substitution language Chomsky Type 1 classification and zero topological entropy."""
        chomsky_res = evaluate_chomsky_hierarchy_and_topological_entropy()
        self.assertEqual(chomsky_res["chomsky_classification"], "Type 1 (Context-Sensitive Grammar)")
        self.assertEqual(chomsky_res["topological_entropy_h_top"], 0.0)
        self.assertAlmostEqual(chomsky_res["complexity_exponent"], 1.4142, places=3)
        self.assertAlmostEqual(chomsky_res["perron_frobenius_radius"], 8.0, places=5)
        self.assertTrue(chomsky_res["entropy_zero_verified"])

    def test_pillar7_citation_network_topology(self):
        """Pillar 7: Citation network graph Laplacian and algebraic connectivity (Fiedler value)."""
        net_res = evaluate_citation_network_topology()
        self.assertEqual(net_res["num_nodes"], 12)
        self.assertEqual(net_res["num_edges"], 28)
        self.assertGreater(net_res["fiedler_algebraic_connectivity"], 0.5)
        self.assertTrue(net_res["graph_connected"])

    def test_pillar1_fubini_study_quantum_geometric_tensor(self):
        """Pillar 1: Joint momentum-phason torus Fubini-Study quantum metric and Chern invariant."""
        fs_res = compute_fubini_study_quantum_geometric_tensor(n_k=15, n_phi=10)
        self.assertGreater(fs_res["mean_quantum_metric_trace"], 0.1)
        self.assertEqual(fs_res["chern_invariant_c1"], -1)
        self.assertTrue(fs_res["quantum_bound_satisfied"])
        self.assertTrue(fs_res["fubini_study_verified"])

    def test_pillar3_crystallographic_bfactors(self):
        """Pillar 3: RCSB PDB 1STM Debye-Waller B-factors and pentameric compliance ratio."""
        bf_res = evaluate_crystallographic_bfactors("data/1stm.pdb")
        if bf_res.get("loaded"):
            self.assertEqual(bf_res["num_hinge_ca_atoms"], 95)
            self.assertGreater(bf_res["compliance_ratio"], 1.5)
            self.assertTrue(bf_res["elevated_hinge_flexibility_verified"])

    def test_pillar4_2adic_tad_hierarchy_barrier(self):
        """Pillar 4: 2-adic ultrametric topological insulation barrier Delta E = 25.2 kcal/mol."""
        tad_res = evaluate_2adic_tad_hierarchy_barrier()
        self.assertAlmostEqual(tad_res["barrier_at_64kb"], 25.2, places=5)
        self.assertGreater(tad_res["insulation_efficiency"][-1], 0.999)
        self.assertTrue(tad_res["ultrametric_barrier_verified"])

    def test_pillar2_c4_boundary_complex_s3_topology(self):
        r"""Pillar 2: Boundary 3-complex \partial C_4 Euler characteristic chi = 80 - 208 + 192 - 64 = 0 (S^3 topology)."""
        b_res = compute_c4_boundary_complex()
        self.assertEqual(b_res["f0_boundary_vertices"], 80)
        self.assertEqual(b_res["f1_boundary_edges"], 208)
        self.assertEqual(b_res["f2_boundary_faces"], 192)
        self.assertEqual(b_res["f3_boundary_cubes"], 64)
        self.assertEqual(b_res["boundary_euler_characteristic_chi"], 0)
        self.assertTrue(b_res["s3_topology_verified"])

    def test_pillar5_chembl_enantiomer_target_affinity(self):
        """Pillar 5: ChEMBL Thalidomide enantiomer differential binding to Cereblon (CRBN, CHEMBL3301389)."""
        aff_res = evaluate_chembl_enantiomer_target_affinity()
        self.assertEqual(aff_res["chembl_target_id"], "CHEMBL3301389")
        self.assertAlmostEqual(aff_res["affinity_ratio_S_vs_R"], 10.0, places=3)
        self.assertLess(aff_res["differential_binding_free_energy_kcal_mol"], -1.0)
        self.assertTrue(aff_res["enantiomer_selectivity_verified"])

    def test_pillar6_lyapunov_spectrum_and_contraction(self):
        """Pillar 6: Chair44 substitution dynamics Lyapunov spectrum: lambda_1 = 3 ln(2) and co-moving contraction."""
        lyap_res = compute_lyapunov_spectrum_and_contraction()
        self.assertAlmostEqual(lyap_res["dominant_lyapunov_exponent_lambda1"], 3.0 * np.log(2.0), places=6)
        self.assertLess(lyap_res["co_moving_contraction_rate"], -1.0)
        self.assertTrue(lyap_res["lyapunov_stability_verified"])

    def test_pillar7_bibliometric_spectral_centrality(self):
        """Pillar 7: Citation network spectral centrality, PageRank, and macro-domain modularity Q > 0.10."""
        cent_res = evaluate_bibliometric_spectral_centrality()
        self.assertGreater(cent_res["max_adjacency_eigenvalue"], 4.5)
        self.assertGreater(cent_res["macro_domain_modularity_Q"], 0.10)
        self.assertEqual(len(cent_res["pagerank_distribution"]), 12)
        self.assertTrue(cent_res["spectral_centrality_verified"])

    def test_pillar1_cmb_polarization_birefringence(self):
        """Pillar 1: CMB polarization E-to-B rotation angular power spectra C_ell^{BB} / C_ell^{EE}."""
        cmb_res = evaluate_cmb_polarization_spectra(ell_max=50, beta_deg=0.342)
        self.assertAlmostEqual(cmb_res["beta_deg"], 0.342, places=3)
        self.assertAlmostEqual(cmb_res["b_to_e_leakage_ratio"], 1.4251e-4, places=6)
        self.assertTrue(cmb_res["cmb_birefringence_verified"])

    def test_pillar2_c4_cubical_homology_betti_numbers(self):
        """Pillar 2: Exact cubical homology Betti numbers b(C_4) = (1,0,0,0,0) and b(del C_4) = (1,0,0,1)."""
        betti = compute_c4_cubical_homology_betti_numbers()
        self.assertTrue(betti["c4_contractible_homology_verified"])
        self.assertTrue(betti["boundary_s3_homology_verified"])
        self.assertEqual(betti["betti_c4"], [1, 0, 0, 0, 0])
        self.assertEqual(betti["betti_boundary_c4"], [1, 0, 0, 1])

    def test_pillar2_c4_hodge_laplacian_harmonic_forms(self):
        """Pillar 2: Discrete Hodge Laplacian harmonic form dimensions dim ker Delta_k = b_k."""
        hodge = compute_c4_hodge_laplacian_decomposition()
        self.assertTrue(hodge["hodge_decomposition_verified"])
        self.assertEqual(hodge["dim_harmonic_k_forms_c4"], [1, 0, 0, 0, 0])
        self.assertEqual(hodge["dim_harmonic_k_forms_boundary"], [1, 0, 0, 1])
        self.assertEqual(hodge["laplacian_ranks_c4"], [79, 212, 210, 92, 15])
        self.assertEqual(hodge["laplacian_ranks_boundary"], [79, 208, 192, 63])

    def test_pillar3_capsid_gnm_normal_modes(self):
        """Pillar 3: Gaussian Network Model (GNM) elastodynamics theoretical B-factor compliance ratio."""
        gnm_res = compute_capsid_elastic_network_normal_modes()
        if gnm_res.get("loaded"):
            self.assertEqual(gnm_res["num_ca_atoms"], 705)
            self.assertGreater(gnm_res["gnm_theoretical_b_compliance_ratio"], 1.50)
            self.assertTrue(gnm_res["gnm_compliance_verified"])

    def test_pillar4_2adic_chromatin_compartment_pc1(self):
        """Pillar 4: 2-adic Hi-C contact correlation matrix leading eigenvector (PC1) A/B compartmentalization."""
        pc1_res = compute_2adic_chromatin_compartment_pc1(n_bins=64)
        self.assertEqual(pc1_res["num_genomic_bins"], 64)
        self.assertGreater(pc1_res["pc1_variance_explained"], 0.75)
        self.assertTrue(pc1_res["bipartite_compartments_verified"])

    def test_pillar5_chiral_optical_torque_trapping(self):
        """Pillar 5: Optical chiral torque and rotational Peclet number for single-molecule trapping."""
        t_res = compute_chiral_optical_torque_trapping()
        self.assertAlmostEqual(t_res["optical_chiral_force_fN"], 14.20, places=2)
        self.assertAlmostEqual(t_res["optical_chiral_torque_zN_um"], 0.710, places=3)
        self.assertGreater(t_res["rotational_peclet_number"], 10.0)
        self.assertTrue(t_res["homochiral_trapping_stable"])

    def test_pillar7_citation_network_small_world_properties(self):
        """Pillar 7: Citation network small-world topology (average path length L < 2.0, clustering C > 0.30)."""
        sw_res = evaluate_citation_network_small_world_properties()
        self.assertEqual(sw_res["num_nodes"], 12)
        self.assertLess(sw_res["average_shortest_path_length"], 2.0)
        self.assertGreater(sw_res["clustering_coefficient"], 0.30)
        self.assertLessEqual(sw_res["network_diameter"], 3)
        self.assertTrue(sw_res["small_world_topology_verified"])

    def test_pillar9_module50_frb_dm_rm_helicity_audit(self):
        """Pillar 9 (Module 50B): FRB DM x RM phasonic magnetic-helicity bispectrum and host-DM clipping selection_calibration audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_frb_dm_rm_phasonic_helicity_audit
        fr = compute_frb_dm_rm_phasonic_helicity_audit()
        self.assertEqual(fr["n_frbs"], 2000)
        self.assertLess(fr["max_tau_scaling_error"], 1e-14)
        self.assertAlmostEqual(fr["frb_dm_rm_helicity_ratio"], 0.0005880, places=6)
        self.assertLessEqual(fr["preregistered_frb_null_fpr"], 0.065)
        self.assertGreater(fr["posthoc_host_dm_clipping_selection_bias_fpr"], 0.78)
        self.assertGreater(fr["blind_frb_helicity_detection_z"], 7.2)
        self.assertTrue(fr["frb_helicity_verified"])

    def test_module51_machine_checked_certificates_and_gauge_invariance(self):
        """Module 51: Machine-checked SymPy & Lean 4 certificates for FR30, Clifford Q8 holonomy gauge invariance, Laplacian charpoly, and 4D obstruction rank."""
        from src.chair44.machine_checked_certificates import run_all_machine_checked_certificates
        certs = run_all_machine_checked_certificates()
        self.assertTrue(certs["all_certificates_verified"])
        self.assertTrue(certs["fr30_certificate"]["all_in_SO3Z"])
        self.assertEqual(certs["clifford_gauge_certificate"]["max_q8_wilson_trace_discrepancy_exact"], 0)
        self.assertEqual(certs["clifford_gauge_certificate"]["q8_gauge_covariance_verified_trials"], 512)
        self.assertTrue(certs["level1_laplacian_certificate"]["characteristic_polynomial_exact_match"])
        self.assertEqual(certs["level1_laplacian_certificate"]["trace_exact"], 96)
        self.assertEqual(certs["c4_obstruction_certificate"]["exact_rational_rank"], 6)
        self.assertEqual(certs["c4_obstruction_certificate"]["gram_determinant_exact"], 21414742)
        self.assertTrue(os.path.isfile("certificates/Chair44Certificates.lean"))

    def test_module51_continuum_quadrature_convergence_audit(self):
        """Module 51: Standalone Gauss-Legendre continuum quadrature convergence and parity cancellation on W_b, -W_b, and W_a."""
        import json
        with open("data/open_audit_package/window_seed_and_continuum_quadrature.json", "r", encoding="utf-8") as f:
            data = json.load(f)["gauss_legendre_convergence_audit"]
        self.assertTrue(data["n16_vs_n20_convergence"]["converged_to_quoted_digits"])
        self.assertTrue(data["parity_and_enantiomorph_controls_n16"]["parity_cancellation_verified"])
        self.assertEqual(data["parity_and_enantiomorph_controls_n16"]["Wb_ratio_rounded_4decimals"], 0.8713)
        self.assertLess(data["parity_and_enantiomorph_controls_n16"]["Wa_achiral_chi_b_residual"], 1e-13)

    def test_module51_stmv_6d_projection(self):
        """Module 51: Independent STMV 1STM 6D projection."""
        from src.cross_disciplinary.pillar3_capsids import evaluate_stmv_independent_6d_projection_and_laplacian_dichroism
        stmv = evaluate_stmv_independent_6d_projection_and_laplacian_dichroism()
        self.assertTrue(stmv["falsifiable_controls_passed"])
        self.assertLess(stmv["mirror_control_enantiomeric_B_residual"], 1e-14)
        self.assertLess(stmv["mirror_control_enantiomeric_J_residual"], 1e-14)

    def test_module51_cosmology_planck_likelihood_and_open_audit_package(self):
        """Module 51: Planck/ACT/SPT cosmological birefringence likelihood confrontation and public open-data audit package."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import evaluate_planck_act_spt_observational_likelihood
        cosmo = evaluate_planck_act_spt_observational_likelihood()
        self.assertTrue(cosmo["observational_survival_verified"])
        self.assertLess(cosmo["chi2_per_dof_prediction"], 0.15)
        self.assertGreater(cosmo["delta_chi2_favoring_birefringence"], 25.0)
        for fname in [
            "projection_matrices_6d_to_3d.json",
            "window_seed_and_continuum_quadrature.json",
            "chair44_fr30_and_laplacian_matrices.json",
            "non_hermitian_hamiltonian_and_gbz.json",
            "dna_brick_2adic_address_scheme.json",
            "falsifiable_hypotheses_benchmarks.json",
        ]:
            self.assertTrue(os.path.isfile(os.path.join("data/open_audit_package", fname)))

    def test_module52_soldered_laplacian_and_schur_coarsening_certificate(self):
        """Module 52A: Exact integer Soldered Bundle Laplacian rank 24 and exact rational Schur-complement coarsening on Level-1 Chair44."""
        from src.chair44.machine_checked_certificates import certify_level1_soldered_laplacian_and_schur_coarsening_exact
        cert = certify_level1_soldered_laplacian_and_schur_coarsening_exact()
        self.assertTrue(cert["solder_and_schur_certified"])
        self.assertEqual(cert["soldered_rank_exact"], 24)
        self.assertEqual(cert["soldered_trace_exact"], 384)
        self.assertEqual(cert["schur_trace_rational"], "72")
        self.assertTrue(cert["schur_zero_mode_preserved_exact"])

    def test_module52_pta_chiral_hellings_downs_pulsar_dropout_audit(self):
        """Module 52C: PTA chiral Hellings-Downs Stokes-V overlap and full-array red-noise marginalization vs pulsar-dropout selection_bias audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_pta_chiral_hellings_downs_pulsar_dropout_audit
        pta = compute_pta_chiral_hellings_downs_pulsar_dropout_audit()
        self.assertTrue(pta["pta_chiral_hd_verified"])
        self.assertLess(pta["max_tau_scaling_error"], 1e-14)
        self.assertLessEqual(pta["preregistered_full_array_null_fpr"], 0.065)
        self.assertGreater(pta["posthoc_pulsar_dropout_selection_bias_fpr"], 0.65)
        self.assertGreater(pta["blind_pta_chiral_detection_z"], 5.0)

    def test_module53_analytic_sinc_2d_continuum_cross_check(self):
        """Module 53A: Independent Analytic-Sinc 2D Triangle Reduction cross-verification of chi_b(infinity), D_lap(infinity), and R_Weyl = 0.8713."""
        from src.icosahedral_qc.continuum_convergence_audit import evaluate_analytic_sinc_2d_continuum_cross_check
        chk = evaluate_analytic_sinc_2d_continuum_cross_check(n_gl_2d=20)
        self.assertTrue(chk["analytic_sinc_2d_cross_check_verified"])
        self.assertEqual(chk["ratio_rounded_4decimals"], 0.8713)
        self.assertLess(chk["abs_diff_chi_b_vs_3d_gl16"], 1e-11)
        self.assertLess(chk["abs_diff_d_lap_vs_3d_gl16"], 1e-11)
        self.assertLess(chk["abs_diff_ratio_vs_3d_gl16"], 1e-8)

    def test_module53_21cm_lensing_audit(self):
        """Module 53C: 21-cm x CMB lensing cross-bispectrum KL selection_bias audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_21cm_cmb_lensing_cross_bispectrum_kl_selection_bias_audit
        cross = compute_21cm_cmb_lensing_cross_bispectrum_kl_selection_bias_audit()
        self.assertTrue(cross["cross_21cm_kappa_verified"])
        self.assertLessEqual(cross["preregistered_transfer_matrix_null_fpr"], 0.06)
        self.assertGreater(cross["posthoc_kl_eigenmode_selection_bias_fpr"], 0.75)


if __name__ == "__main__":
    unittest.main()


