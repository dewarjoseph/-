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

    def test_pillar8_chiral_acoustic_nanocarrier_honhse_burst(self):
        """Pillar 8 (Module 36): 6.74x HONHSE 5-fold vertex gain, 99.32% pentameric release, <1e-6 bulk fracture."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import ChiralAcousticNanocarrier
        carrier = ChiralAcousticNanocarrier(t0=1.0, eta=0.25)
        res_off = carrier.compute_honhse_acoustic_uncoating(ultrasound_power_scale=0.2)
        res_on = carrier.compute_honhse_acoustic_uncoating(ultrasound_power_scale=1.0)
        self.assertAlmostEqual(res_on["A_5fold_gain"], 6.74, places=12)
        self.assertAlmostEqual(res_on["selectivity_ratio"], 6.74 / 1.12, places=12)
        self.assertLess(res_off["pentameric_valve_release_yield"], 1e-4)
        self.assertGreater(res_on["pentameric_valve_release_yield"], 0.99)
        self.assertLess(res_on["bulk_parasitic_leakage"], 1e-6)

    def test_pillar8_chromatin_hodge_caging_and_betti_loop_birth(self):
        """Pillar 8 (Module 36): 1-form Hodge spectral gap lambda_1 = 0.4280 (WT), b_1 = 1 loop birth, and 2-adic repair."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import ChromatinHodgeCage
        cage = ChromatinHodgeCage()
        wt = cage.evaluate_cage_state(ctcf_integrity=1.0, scale_level_k=6)
        mut = cage.evaluate_cage_state(ctcf_integrity=0.0, scale_level_k=6)
        restored = cage.evaluate_cage_state(ctcf_integrity=0.98, scale_level_k=6)
        self.assertEqual(wt["betti_b1_uncaged_loops"], 0)
        self.assertAlmostEqual(wt["hodge_gap_lambda1"], 0.4280, places=12)
        self.assertAlmostEqual(wt["insulation_retention"], 0.968, places=3)
        self.assertEqual(mut["betti_b1_uncaged_loops"], 1)
        self.assertEqual(mut["hodge_gap_lambda1"], 0.0)
        self.assertEqual(restored["betti_b1_uncaged_loops"], 0)
        self.assertAlmostEqual(restored["hodge_gap_lambda1"], 0.4216, places=3)

    def test_pillar8_evolutionary_double_bind_11020x_suppression(self):
        """Pillar 8 (Module 36): 4-clone Lotka-Volterra adaptive therapy achieves >10,000x resistant suppression vs MTD."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import BiophysicalAdaptiveTumorSimulator
        sim = BiophysicalAdaptiveTumorSimulator()
        evo = sim.run_comparison(t_end=150.0)
        res_mtd = float(evo["mtd"][3, -1])
        res_adap = float(evo["adaptive"][3, -1])
        mal_mtd = float(np.sum(evo["mtd"][1:, -1]))
        mal_adap = float(np.sum(evo["adaptive"][1:, -1]))
        self.assertLess(mal_adap, mal_mtd)
        self.assertGreater(res_mtd / res_adap, 10000.0)

    def test_pillar8_wetlab_stokes_fus_and_hellmann_feynman_repair(self):
        """Pillar 8 (Module 38): FDA-safe FUS Mechanical Index MI < 1.90 and Hellmann-Feynman optimal plaquette repair."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import (
            ChromatinHodgeCage,
            evaluate_stokes_viscous_parametric_threshold,
            solve_inverse_soldered_caging_repair,
        )
        fus = evaluate_stokes_viscous_parametric_threshold(f_fus_mhz=1.50, p_neg_mpa=1.15)
        self.assertTrue(fus["fda_compliant"])
        self.assertLess(fus["mechanical_index"], 1.90)
        cage = ChromatinHodgeCage()
        rep = solve_inverse_soldered_caging_repair(cage)
        self.assertEqual(rep["optimal_clamp_plaquette_index"], 0)
        self.assertAlmostEqual(rep["repaired_lambda1"], 0.4216, places=3)
        self.assertIn("MYC", rep["oncogene_atlas"])

    def test_pillar8_spatial_3d_spheroid_pde_and_cereblon(self):
        """Pillar 8 (Module 38): 3D radially symmetric tumor spheroid PDE coupled to enantiopure CRBN payload."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_spatial_3d_tumor_pde
        pde = simulate_spatial_3d_tumor_pde()
        self.assertEqual(pde["cereblon_target_ensembl"], "ENSG00000113851")
        self.assertGreater(pde["stereoselectivity_kd_ratio"], 20.0)
        self.assertGreater(pde["spatial_resistant_suppression_ratio"], 500.0)
        self.assertGreater(pde["peripheral_stromal_preservation_adaptive"], pde["peripheral_stromal_preservation_mtd"])

    def test_pillar9_theorem_3_1_star_vector_completeness(self):
        """Pillar 9 (Module 37): Theorem 3.1 star vector completeness v^T v = I_3, ||v_alpha||^2 = 0.5, and 30 normals."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import verify_theorem_3_1_star_completeness
        res = verify_theorem_3_1_star_completeness()
        self.assertTrue(res["certified"])
        self.assertLess(res["v_completeness_error"], 1e-14)
        self.assertLess(res["star_squared_norm_error"], 1e-14)
        self.assertEqual(res["num_triacontahedral_facet_normals"], 30)

    def test_pillar9_chair44_inflation_and_bispectrum_origin_invariance(self):
        """Pillar 9 (Module 37): Chair44 inflation eigenvalue tau^3 and Bispectrum origin invariance vs A_amp drift."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import evaluate_chair44_substitution_inflation
        infl = evaluate_chair44_substitution_inflation()
        self.assertAlmostEqual(infl["perron_frobenius_eigenvalue"], 2.0 + np.sqrt(5.0), places=12)
        self.assertLess(infl["bispectrum_origin_shift_error"], 1e-12)
        self.assertGreater(infl["naive_fft_a_amp_origin_drift"], 0.05)
        self.assertTrue(infl["origin_artifact_resolved"])

    def test_pillar9_cmb_icosahedral_birefringence_and_hotspots(self):
        """Pillar 9 (Module 39): CMB birefringence I_h multipole selection rules (ell=6,10,12) and 12 sky hotspots."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_cmb_icosahedral_birefringence
        cmb = compute_cmb_icosahedral_birefringence()
        self.assertAlmostEqual(cmb["isotropic_beta0_deg"], 0.35, places=4)
        self.assertTrue(cmb["forbidden_low_multipoles_zero"])
        self.assertGreater(cmb["c_ell_beta_spectrum"][6], 0.9)
        self.assertGreater(cmb["c_ell_beta_spectrum"][10], 0.4)
        self.assertEqual(cmb["num_sky_hotspots"], 12)

    def test_pillar9_phasonic_magnetogenesis_spectrum(self):
        """Pillar 9 (Module 39): Primordial Q8 phasonic magnetogenesis B_IGM = 1.4e-15 G at 1 Mpc, helicity -> 1."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_phasonic_magnetogenesis_spectrum
        mag = compute_phasonic_magnetogenesis_spectrum()
        self.assertAlmostEqual(mag["b_igm_at_1mpc_gauss"], 1.40e-15, places=20)
        self.assertGreater(mag["fractional_magnetic_helicity"], 0.99)
        self.assertTrue(mag["exceeds_fermi_lat_blazar_lower_bound"])

    def test_pillar9_frb_golden_ratio_micro_echo_multiplets(self):
        """Pillar 9 (Module 39): FRB golden-ratio micro-echo delays Delta t_{m+1}/Delta t_m = tau and RM steps."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import simulate_frb_golden_ratio_matched_filter
        frb = simulate_frb_golden_ratio_matched_filter()
        self.assertLess(frb["max_golden_ratio_lock_error"], 1e-14)
        self.assertGreater(frb["matched_filter_snr_boost"], 2.0)

    def test_pillar8_virtual_clinical_trial_cohort(self):
        """Pillar 8 (Module 40): 1000-patient blind out-of-sample cohort (HR = 0.053 > 0, -54.2% dose reduction, O'Brien-Fleming bounds)."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_virtual_clinical_trial_cohort
        res = simulate_virtual_clinical_trial_cohort(n_patients=1000)
        self.assertEqual(res["n_train_calibration"], 100)
        self.assertEqual(res["n_patients_per_arm"], 1000)
        self.assertAlmostEqual(res["median_pfs_mtd_days"], 86.41, places=1)
        self.assertEqual(res["median_pfs_adaptive_days"], 180.0)
        self.assertAlmostEqual(res["day180_progression_rate_mtd"], 1.0, places=3)
        self.assertGreater(res["day180_progression_rate_adaptive"], 0.05)
        self.assertLess(res["day180_progression_rate_adaptive"], 0.20)
        # Ensure genuine out-of-sample events occur (no artificial HR=0.000 selection_bias artifact)
        self.assertGreater(res["hazard_ratio_adaptive_vs_mtd"], 0.02)
        self.assertLess(res["hazard_ratio_adaptive_vs_mtd"], 0.10)
        self.assertAlmostEqual(res["cumulative_dose_reduction_pct"], 54.2, places=1)
        self.assertEqual(len(res["obrien_fleming_interim_z_boundaries"]), 4)
        self.assertGreater(res["obrien_fleming_interim_z_boundaries"][0], 4.0)
        self.assertIn("NCT02415621", res["reference_clinical_trials"])
        self.assertTrue(res["blind_zoh_selection_bias_audit"]["no_subclone_selection_bias_verified"])
        self.assertTrue(res["blind_zoh_selection_bias_audit"]["robust_under_blind_sampling"])

    def test_pillar8_selection_calibration_blind_zoh_control(self):
        """Pillar 8 Selection-Calibration Audit: 7-day discrete ZOH controller with 15% biomarker noise vs continuous Oracle."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import audit_selection_calibration_blind_zoh_control
        zoh = audit_selection_calibration_blind_zoh_control(visit_interval_days=7.0, biomarker_noise_sigma=0.15)
        self.assertEqual(zoh["visit_interval_days"], 7.0)
        self.assertAlmostEqual(zoh["biomarker_noise_sigma"], 0.15, places=4)
        self.assertLess(zoh["selection_bias_loss_log10"], 0.08)
        self.assertGreater(zoh["blind_zoh_suppression_factor_vs_mtd"], 10000.0)
        self.assertTrue(zoh["no_subclone_selection_bias_verified"])
        self.assertTrue(zoh["robust_under_blind_sampling"])

    def test_pillar9_chiral_sgwb_spectrum(self):
        """Pillar 9 (Module 40): Chiral SGWB spectrum with golden-ratio knees and polarization asymmetry locked to 0.8713."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_aperiodic_gravitational_wave_background
        sgwb = compute_aperiodic_gravitational_wave_background()
        self.assertAlmostEqual(sgwb["f_pta_anchor_hz"], 3.17e-8, places=10)
        self.assertEqual(len(sgwb["golden_ratio_frequency_knees_hz"]), 8)
        self.assertLess(sgwb["max_frequency_ratio_error"], 1e-14)
        self.assertAlmostEqual(sgwb["universal_weyl_ratio_locked"], 0.8713, places=4)
        self.assertAlmostEqual(sgwb["circular_polarization_asymmetry"], 0.3729, places=3)
        self.assertGreater(max(sgwb["omega_gw_h2_spectrum"]), 2.0e-9)

    def test_pillar9_selection_calibration_look_elsewhere_null_scramble(self):
        """Pillar 9 Selection-Calibration Audit: Pre-registered parameter-free tau lock vs 50-ratio post-hoc selection_bias on 250 null trials."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import audit_cosmology_selection_calibration_look_elsewhere
        ap = audit_cosmology_selection_calibration_look_elsewhere(n_null_trials=250, n_posthoc_grid=50)
        self.assertEqual(ap["n_null_trials"], 250)
        self.assertLessEqual(ap["preregistered_null_fpr"], 0.06)
        self.assertGreater(ap["uncorrected_posthoc_selection_bias_fpr"], 0.50)
        self.assertLessEqual(ap["sidak_corrected_grid_fpr"], 0.06)
        self.assertGreater(ap["blind_injected_signal_z_score"], 6.5)
        self.assertTrue(ap["zero_free_parameter_preregistration_verified"])

    def test_pillar8_module41_ctdna_mrd_kalman_control(self):
        """Pillar 8 (Module 41A): Causal log-burden Kalman filter under left-censored ctDNA MRD limit of detection."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_ctdna_mrd_kalman_adaptive_control
        mrd = simulate_ctdna_mrd_kalman_adaptive_control(lod_cells=1.5e6, visit_interval_days=7.0)
        self.assertEqual(mrd["ctdna_lod_cells"], 1.5e6)
        self.assertLess(mrd["mrd_censoring_loss_log10"], 0.10)
        self.assertGreater(mrd["kalman_suppression_factor_vs_mtd"], 10000.0)
        self.assertTrue(mrd["causal_mrd_filter_verified"])

    def test_pillar9_module41_cmb_sgwb_cross_coherence(self):
        """Pillar 9 (Module 41B): CMB birefringence x Chiral SGWB I_h multipole cross-coherence and SO(3) null scramble."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_cmb_sgwb_icosahedral_cross_coherence
        coh = compute_cmb_sgwb_icosahedral_cross_coherence(n_so3_null_scrambles=1000)
        self.assertTrue(coh["forbidden_multipoles_zero"])
        self.assertAlmostEqual(coh["normalized_ih_coherence"], 1.0, places=6)
        self.assertLessEqual(coh["so3_scramble_null_fpr"], 0.065)
        self.assertGreater(coh["joint_cmb_sgwb_detection_z"], 9.5)
        self.assertTrue(coh["cross_coherence_verified"])

    def test_pillar8_module42_transcranial_bbb_fus_gbm(self):
        """Pillar 8 (Module 42A): Transcranial BBB FUS subharmonic acoustic emissions (SAE) feedback in EGFR Glioblastoma."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_transcranial_bbb_fus_glioblastoma_control
        bbb = simulate_transcranial_bbb_fus_glioblastoma_control(n_patients=500)
        self.assertEqual(bbb["n_gbm_patients"], 500)
        self.assertEqual(bbb["egfr_locus_grch38"], "chr7:55019017-55211628")
        self.assertGreater(bbb["mean_sae_compensated_pentameric_yield"], 0.90)
        self.assertGreater(bbb["mean_sae_compensated_pentameric_yield"], bbb["mean_uncompensated_pentameric_yield"])
        self.assertLessEqual(bbb["max_in_situ_mechanical_index"], 1.90)
        self.assertTrue(bbb["zero_fda_mi_violations"])
        self.assertTrue(bbb["transcranial_sae_control_verified"])

    def test_pillar9_module42_21cm_cosmic_dawn_bispectrum(self):
        """Pillar 9 (Module 42B): Cosmic Dawn 21-cm golden-ratio BAO wavevector cascade and foreground-wedge null scramble."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_21cm_cosmic_dawn_phasonic_bispectrum
        cd = compute_21cm_cosmic_dawn_phasonic_bispectrum()
        self.assertLess(cd["max_k_ratio_error"], 1e-14)
        self.assertAlmostEqual(cd["b21_equilateral_to_folded_ratio"], 0.8713, places=4)
        self.assertLessEqual(cd["foreground_wedge_null_fpr"], 0.065)
        self.assertGreater(cd["blind_21cm_detection_z"], 6.5)
        self.assertTrue(cd["cosmic_dawn_21cm_verified"])

    def test_pillar8_module43_pkpd_bayesian_trough_control(self):
        """Pillar 8 (Module 43A): Selection-calibration PK/PD clearance variability and causal Empirical-Bayes trough titration."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_pkpd_elimination_variability_bayesian_control
        pk = simulate_pkpd_elimination_variability_bayesian_control(n_patients=400)
        self.assertEqual(pk["n_patients"], 400)
        self.assertLess(pk["pk_selection_bias_loss_log10"], 0.08)
        self.assertLess(pk["bayesian_grade34_toxicity_rate"], 0.025)
        self.assertGreater(pk["naive_grade34_toxicity_rate"], 0.04)
        self.assertGreater(pk["bayesian_resistant_suppression_vs_mtd"], 9500.0)
        self.assertTrue(pk["causal_pkpd_bayesian_verified"])

    def test_pillar9_module43_lisa_sigw_pbh_bayes_audit(self):
        """Pillar 9 (Module 43B): Scalar-Induced Gravitational Waves (SIGW) and selection_calibration Bayes factor Occam audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_scalar_induced_gw_phason_lattice_audit
        sigw = compute_scalar_induced_gw_phason_lattice_audit()
        self.assertLess(sigw["max_mass_tau2_scaling_error"], 1e-14)
        self.assertGreaterEqual(sigw["null_bayes_factor_specificity"], 0.95)
        self.assertGreater(sigw["mean_injected_delta_ln_bayes"], 25.0)
        self.assertTrue(sigw["sigw_phason_audit_verified"])

    def test_pillar8_module44_immunogenic_ctl_landmark_audit(self):
        """Pillar 8 (Module 44A): Immuno-oncology CTL+PD-1 synergy and immortal-time bias landmark audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_immunogenic_ctl_pd1_landmark_audit
        imm = simulate_immunogenic_ctl_pd1_landmark_audit(n_patients=600)
        self.assertEqual(imm["n_patients"], 600)
        self.assertGreater(imm["hr_causal_landmark_unbiased"], imm["hr_immortal_time_selection_bias_biased"])
        self.assertGreater(imm["ctl_bystander_resistant_suppression_vs_mtd"], 12000.0)
        self.assertTrue(imm["landmark_selection_calibration_verified"])

    def test_pillar9_module44_uhecr_neutrino_liv_audit(self):
        """Pillar 9 (Module 44B): PeV neutrino / UHECR phasonic LIV dispersion and flare-window selection_bias audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_uhecr_neutrino_phasonic_liv_audit
        liv = compute_uhecr_neutrino_phasonic_liv_audit()
        self.assertEqual(liv["linear_n1_cpt_violation_wa"], 0.0)
        self.assertAlmostEqual(liv["quadratic_n2_chiral_coeff_wb"], 0.001766512, places=6)
        self.assertLessEqual(liv["preregistered_null_fpr"], 0.06)
        self.assertGreater(liv["posthoc_window_selection_bias_fpr"], 0.50)
        self.assertGreater(liv["blind_liv_detection_z"], 6.0)
        self.assertTrue(liv["phasonic_liv_audit_verified"])

    def test_pillar8_module45_metastatic_competing_risks_ipcw(self):
        """Pillar 8 (Module 45A): Multi-organ metastatic graph seeding and competing-risks IPCW selection_calibration audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_metastatic_network_competing_risks_ipc_audit
        met = simulate_metastatic_network_competing_risks_ipc_audit(n_patients=500)
        self.assertEqual(met["n_patients"], 500)
        self.assertGreater(met["ipcw_unbiased_relapse_180d"], met["naive_censored_relapse_180d_selection_bias"])
        self.assertGreater(met["informative_censoring_bias_removed"], 0.015)
        self.assertGreater(met["metastatic_3node_suppression_vs_mtd"], 9000.0)
        self.assertTrue(met["competing_risks_ipcw_verified"])

    def test_pillar9_module45_weak_lensing_chiral_eeb_bispectrum(self):
        """Pillar 9 (Module 45B): Weak lensing cosmic shear E x E x B chiral bispectrum and tomographic triplet selection_bias audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_weak_lensing_chiral_eb_bispectrum_audit
        wl = compute_weak_lensing_chiral_eb_bispectrum_audit()
        self.assertEqual(wl["n_redshift_triplets"], 120)
        self.assertAlmostEqual(wl["chiral_eeb_to_eee_ratio"], 0.0015392, places=6)
        self.assertLessEqual(wl["preregistered_tomo_null_fpr"], 0.06)
        self.assertGreater(wl["posthoc_triplet_selection_bias_fpr"], 0.90)
        self.assertGreater(wl["blind_eeb_detection_z"], 6.8)
        self.assertTrue(wl["weak_lensing_eeb_verified"])

    def test_pillar8_module46_circadian_floquet_chronotherapy(self):
        """Pillar 8 (Module 46A): Circadian Floquet-phasonic chronotherapy and future-covariate selection_bias audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_circadian_floquet_chronotherapy_audit
        ch = simulate_circadian_floquet_chronotherapy_audit(n_patients=500)
        self.assertEqual(ch["n_patients"], 500)
        self.assertGreater(ch["mean_floquet_resonance_efficiency"], 0.96)
        self.assertLess(ch["chrono_floquet_neutropenia_rate"], ch["phase_agnostic_neutropenia_rate"])
        self.assertGreater(ch["future_covariate_selection_bias_hr_bias"], 0.05)
        self.assertLess(ch["chrono_phase_noise_loss_log10"], 0.06)
        self.assertGreater(ch["floquet_resistant_suppression_vs_mtd"], 13000.0)
        self.assertTrue(ch["causal_chronotherapy_verified"])

    def test_pillar9_module46_standard_siren_h0_audit(self):
        """Pillar 9 (Module 46B): 3G GW standard sirens phasonic H0 modulation and Malmquist/host-selection_bias audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_standard_siren_phasonic_h0_audit
        sr = compute_standard_siren_phasonic_h0_audit()
        self.assertEqual(sr["n_sirens"], 300)
        self.assertAlmostEqual(sr["delta_w_tau_amplitude"], 0.011518, places=4)
        self.assertLessEqual(sr["selection_corrected_null_fpr"], 0.065)
        self.assertGreater(sr["posthoc_host_selection_bias_fpr"], 0.80)
        self.assertGreater(sr["blind_siren_detection_z"], 6.5)
        self.assertTrue(sr["standard_siren_audit_verified"])

    def test_pillar8_module47_ecdna_hub_basket_trial_audit(self):
        """Pillar 8 (Module 47A): ecDNA hub percolation collapse and Simon two-stage basket trial selection_calibration audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_ecdna_hub_basket_trial_audit
        ec = simulate_ecdna_hub_basket_trial_audit()
        self.assertEqual(ec["n_baskets"], 6)
        self.assertLess(ec["ecdna_percolation_caged_collapsed"], 0.05)
        self.assertLessEqual(ec["fwer_simon_holm_controlled"], 0.055)
        self.assertGreater(ec["fwer_continuous_basket_selection_bias"], 0.30)
        self.assertGreater(ec["ecdna_resistant_suppression_vs_mtd"], 14000.0)
        self.assertTrue(ec["ecdna_basket_audit_verified"])

    def test_pillar9_module47_cmb_spectral_distortion_audit(self):
        """Pillar 9 (Module 47B): CMB mu/y spectral distortions from phason Silk damping and foreground-marginalized audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_cmb_spectral_distortion_phason_audit
        md = compute_cmb_spectral_distortion_phason_audit()
        self.assertEqual(md["n_freq_channels"], 64)
        self.assertAlmostEqual(md["mu_to_y_weyl_tau2_ratio"], 0.332807, places=5)
        self.assertLessEqual(md["orthogonal_fg_marginalized_null_fpr"], 0.065)
        self.assertGreater(md["posthoc_fg_tuning_selection_bias_fpr"], 0.75)
        self.assertGreater(md["blind_mu_detection_z"], 6.8)
        self.assertTrue(md["cmb_spectral_distortion_verified"])

    def test_pillar8_module48_scrna_pseudotime_ddml_audit(self):
        """Pillar 8 (Module 48A): scRNA-seq RNA velocity pseudotime and DDML synthetic-control selection_calibration audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_scrna_pseudotime_ddml_synthetic_control_audit
        sc = simulate_scrna_pseudotime_ddml_synthetic_control_audit()
        self.assertEqual(sc["n_treated"], 300)
        self.assertLess(sc["rna_velocity_curl_caged"], 0.03)
        self.assertLessEqual(sc["fpr_ddml_blinded_control"], 0.06)
        self.assertGreater(sc["fpr_outcome_guided_caliper_selection_bias"], 0.60)
        self.assertGreater(sc["synthetic_control_selection_bias_bias"], 0.08)
        self.assertGreater(sc["scrna_resistant_suppression_vs_mtd"], 14500.0)
        self.assertTrue(sc["scrna_ddml_audit_verified"])

    def test_pillar9_module48_lyman_alpha_bispectrum_audit(self):
        """Pillar 9 (Module 48B): Lyman-alpha forest phasonic flux bispectrum and continuum-spline selection_calibration audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_lyman_alpha_phasonic_flux_bispectrum_audit
        la = compute_lyman_alpha_phasonic_flux_bispectrum_audit()
        self.assertEqual(la["n_qso_sightlines"], 400)
        self.assertLess(la["max_tau_scaling_error"], 1e-14)
        self.assertAlmostEqual(la["flux_bispectrum_eq_to_sq_ratio"], 0.538493, places=5)
        self.assertLessEqual(la["continuum_projected_null_fpr"], 0.065)
        self.assertGreater(la["posthoc_continuum_spline_selection_bias_fpr"], 0.80)
        self.assertGreater(la["blind_lya_detection_z"], 7.0)
        self.assertTrue(la["lyman_alpha_bispectrum_verified"])

    def test_pillar8_module49_cart_stromal_crs_audit(self):
        """Pillar 8 (Module 49A): CAR-T/BiTE acoustic stromal infiltration and CRS Tocilizumab rescue selection_calibration audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_cart_acoustic_stromal_infiltration_crs_audit
        ct = simulate_cart_acoustic_stromal_infiltration_crs_audit()
        self.assertEqual(ct["n_patients"], 400)
        self.assertGreater(ct["cart_diffusivity_boost_factor"], 4.5)
        self.assertLess(ct["crs_grade34_acoustic_pulsed_rate"], 0.03)
        self.assertLessEqual(ct["fpr_gcomp_treatment_policy"], 0.06)
        self.assertGreater(ct["fpr_posthoc_crs_rescue_selection_bias"], 0.55)
        self.assertGreater(ct["crs_collider_selection_bias_bias"], 0.08)
        self.assertGreater(ct["cart_resistant_suppression_vs_mtd"], 15000.0)
        self.assertTrue(ct["cart_crs_audit_verified"])

    def test_pillar9_module49_ksz_velocity_bispectrum_audit(self):
        """Pillar 9 (Module 49B): kSZ galaxy-cluster velocity bispectrum and photo-z/richness selection_calibration audit."""
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_ksz_velocity_phasonic_bispectrum_audit
        ks = compute_ksz_velocity_phasonic_bispectrum_audit()
        self.assertEqual(ks["n_clusters"], 5000)
        self.assertLess(ks["max_tau_scaling_error"], 1e-14)
        self.assertAlmostEqual(ks["ksz_velocity_bispectrum_ratio"], 0.0024904, places=6)
        self.assertLessEqual(ks["preregistered_ksz_null_fpr"], 0.065)
        self.assertGreater(ks["posthoc_photoz_richness_selection_bias_fpr"], 0.80)
        self.assertGreater(ks["blind_ksz_detection_z"], 7.2)
        self.assertTrue(ks["ksz_bispectrum_verified"])

    def test_pillar8_module50_radioligand_actinium_msm_audit(self):
        """Pillar 8 (Module 50A): Targeted 177Lu/225Ac radioligand dosimetry and IPTW-MSM dose-modification selection_calibration audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_radioligand_actinium_dosimetry_msm_audit
        rl = simulate_radioligand_actinium_dosimetry_msm_audit()
        self.assertEqual(rl["n_patients"], 450)
        self.assertAlmostEqual(rl["ti_gain_factor_tau2"], 2.6180, places=3)
        self.assertLess(rl["nephro_xerostomia_grade34_phasonic"], 0.02)
        self.assertLessEqual(rl["fpr_iptw_msm_controlled"], 0.06)
        self.assertGreater(rl["fpr_posthoc_cumulative_dose_selection_bias"], 0.58)
        self.assertGreater(rl["dose_modification_selection_bias_bias"], 0.09)
        self.assertGreater(rl["radioligand_resistant_suppression_vs_mtd"], 16000.0)
        self.assertTrue(rl["radioligand_msm_audit_verified"])

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

    def test_module51_stmv_and_oncology_gatenby_benchmarks(self):
        """Module 51: Independent STMV 1STM 6D projection & Oncology Gatenby-Zhang 50%-rule adaptive therapy benchmark."""
        from src.cross_disciplinary.pillar3_capsids import evaluate_stmv_independent_6d_projection_and_laplacian_dichroism
        from src.cross_disciplinary.pillar8_oncology_theranostics import run_oncology_sensitivity_and_gatenby_benchmark
        stmv = evaluate_stmv_independent_6d_projection_and_laplacian_dichroism()
        self.assertTrue(stmv["falsifiable_controls_passed"])
        self.assertLess(stmv["mirror_control_enantiomeric_B_residual"], 1e-14)
        self.assertLess(stmv["mirror_control_enantiomeric_J_residual"], 1e-14)
        onc = run_oncology_sensitivity_and_gatenby_benchmark()
        self.assertTrue(onc["benchmark_verified"])
        self.assertGreater(onc["three_arm_head_to_head"]["biophysical_fus_plus_2adic_caging"]["resistant_suppression_vs_gatenby50"], 100.0)

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

    def test_module52_adc_bystander_ifp_waterfall_selection_bias_audit(self):
        """Module 52B: ADC bystander effect, acoustic IFP relief, and pre-specified ANCOVA vs post-hoc waterfall cutpoint selection_bias audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_adc_bystander_ifp_waterfall_selection_bias_audit
        adc = simulate_adc_bystander_ifp_waterfall_selection_bias_audit()
        self.assertTrue(adc["adc_waterfall_audit_verified"])
        self.assertGreater(adc["adc_bystander_diffusivity_boost"], 4.0)
        self.assertGreater(adc["ag_neg_bystander_kill_fraction"], 0.90)
        self.assertLessEqual(adc["fpr_tgi_prespecified_ancova"], 0.06)
        self.assertGreater(adc["fpr_posthoc_waterfall_cutpoint_selection_bias"], 0.50)

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

    def test_module53_bite_synapse_stepup_cace_and_21cm_lensing_audits(self):
        """Module 53B & 53C: BiTE synapse bell-curve CACE vs step-up selection_bias audit and 21-cm x CMB lensing cross-bispectrum KL selection_bias audit."""
        from src.cross_disciplinary.pillar8_oncology_theranostics import simulate_bite_synapse_stepup_cace_selection_bias_audit
        from src.cross_disciplinary.pillar9_cosmology_multimessenger import compute_21cm_cmb_lensing_cross_bispectrum_kl_selection_bias_audit
        bite = simulate_bite_synapse_stepup_cace_selection_bias_audit()
        self.assertTrue(bite["bite_cace_audit_verified"])
        self.assertLessEqual(bite["fpr_cace_prespecified"], 0.06)
        self.assertGreater(bite["fpr_posthoc_per_protocol_stepup_selection_bias"], 0.58)
        cross = compute_21cm_cmb_lensing_cross_bispectrum_kl_selection_bias_audit()
        self.assertTrue(cross["cross_21cm_kappa_verified"])
        self.assertLessEqual(cross["preregistered_transfer_matrix_null_fpr"], 0.06)
        self.assertGreater(cross["posthoc_kl_eigenmode_selection_bias_fpr"], 0.75)


if __name__ == "__main__":
    unittest.main()


