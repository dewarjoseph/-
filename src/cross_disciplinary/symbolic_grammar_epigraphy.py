"""
src/cross_disciplinary/symbolic_grammar_epigraphy.py
================================================================================
Bridge module for Symbolic Grammar and Epigraphy.
================================================================================
"""

from src.cross_disciplinary.epigraphy_grammar import (
    compute_contact_language_closure,
    evaluate_entropy_superconvergence,
    restore_corrupted_aperiodic_sequence,
)


def analyze_symbolic_grammar():
    closure = compute_contact_language_closure()
    entropy = evaluate_entropy_superconvergence()
    return {
        "p0_exact_match_30": closure["initial_contact_pairs_P0"] == 30,
        "superconvergence_verified": entropy["superconvergence_rate_alpha"] == 1.0,
        "closure": closure,
        "entropy": entropy,
    }
