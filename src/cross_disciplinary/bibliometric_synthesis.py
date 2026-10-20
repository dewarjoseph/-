"""
src/cross_disciplinary/bibliometric_synthesis.py
================================================================================
Bridge module for Multi-Database Bibliometric Synthesis.
================================================================================
"""

from src.cross_disciplinary.bibliometrics import (
    VERIFIED_BIBLIOGRAPHY,
    generate_comparison_matrix,
)


def generate_bibliometric_matrix():
    matrix = generate_comparison_matrix()
    return {
        "all_dois_and_urls_verified": matrix["num_with_dois"] > 0,
        "total_verified_citations": len(VERIFIED_BIBLIOGRAPHY),
        "matrix": matrix,
    }
