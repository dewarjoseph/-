Commit 47477c7aea9e97802c6a3105bf0e38c415df5128 — L=64 honesty applied; CH-V-020 stays [X].

Independently checked against `/home/box/shared/quasicrystal-materials/diffraction/tables/chair44_L64.json` and `diffraction/prereg/2026-11-06_chair44_L64_prereg_v1.md` (sha256 `10253440709fbe6dfe9c716d010fa1127e1fb2fb73cb72cbe7079a9435fbb547`, matching the JSON field):
- H2 at (3/16, 5/32, 1/64): D1 ratio 0.01796463270465118, D2 0.045059895785677664 — falling [C on patch]; not a resolved Bragg peak.
- H3 at (1/3, 0, 0): ratio 0.2500777662631863, above the locked cut of 0.25 (FAIL); the cut was not moved.
- Computed diffraction of a generated point set, not a measured crystal and not a proof of infinite-hull limit-periodicity. Chair44 stays limit-periodic cubic, not icosahedral.
- This note does not independently verify the live Cookies commit named above.
