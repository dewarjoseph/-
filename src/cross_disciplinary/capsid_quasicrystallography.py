"""
src/cross_disciplinary/capsid_quasicrystallography.py
================================================================================
Bridge module for PDB 1STM Viral Capsid Quasicrystallography.
================================================================================
"""

from src.cross_disciplinary.viral_capsid import (
    generate_idealized_1stm_capsid,
    analyze_viral_capsid_quasicrystallography,
)


def analyze_capsid_quasicrystallography():
    coords, labels = generate_idealized_1stm_capsid(r_capsid=8.0, n_residues_per_subunit=25)
    metrics = analyze_viral_capsid_quasicrystallography(coords)
    metrics["pdb_id"] = "1STM"
    metrics["num_calpha_atoms"] = len(coords)
    metrics["num_subunits"] = len(set(labels))
    return metrics
