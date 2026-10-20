"""
paper/build_36page_monograph.py
================================================================================
Generates the comprehensive 36+ page mathematical physics monograph for paper/main.tex
and compiles to paper/main.pdf with tectonic.
================================================================================
"""

import os
import subprocess
import pypdf

def main():
    print("Generating comprehensive 36+ page monograph...")
    
    # We will write the expanded main.tex with rich mathematical appendices,
    # proofs, detailed tables, and verified data.
    script_path = os.path.abspath("paper/generate_expanded_monograph.py")
    subprocess.run(["python", script_path], check=True)
    
    print("Compiling with tectonic...")
    subprocess.run(["tectonic", "paper/main.tex"], check=True)
    
    reader = pypdf.PdfReader("paper/main.pdf")
    pages = len(reader.pages)
    print(f"Compilation successful! Total PDF pages: {pages}")
    assert pages >= 35, f"PDF page count {pages} is less than required 35 pages!"
    print("[SUCCESS] 35+ page requirement strictly satisfied!")

if __name__ == "__main__":
    main()
