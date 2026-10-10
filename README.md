# srg-parity-lean — Lean 4 formalisation of the parity criterion for strongly regular graphs

Formal proof of the parity corollary (Cor. 4.1), the non-existence of srg(169,42,5,12) (§5.1) and the
NL_m(q) family (Cor. 4.2) of

> A. Kovaľ, *The Bannai–Munemasa–Venkov lattice method for strongly regular graphs: a uniform
> discriminant-form condition and new nonexistence results*, Zenodo, 2026, doi:10.5281/zenodo.23275433.

Lean `v4.35.0-rc4`, Mathlib `021ce68` (same toolchain as
[srg154-lean](https://github.com/tonykoval/srg154-lean)).
No `sorry`, no `native_decide`, no `admit`, no new axioms. Every main theorem's `#print axioms` is
`[propext, Classical.choice, Quot.sound]`; see `Axioms.lean` and `tools/axioms_output.txt`.

## What is proved (all formal, no hypotheses beyond the statements)

| Lean theorem | paper | statement |
|---|---|---|
| `Parity.even_det_odd` (`EvenLattice.lean`) | (F5) | `G : Matrix ι ι ℤ` symmetric, even diagonal, `det G` odd ⇒ `card ι = 2h` and `det G ≡ (-1)^h (mod 4)` |
| `Parity.centred_lattice` (`Centred.lean`) | Lemma `lem:dual`(2) + proof of Cor. 4.1 | `G` symmetric integral, constant even diagonal `ν`, `G² = ℓG`, `ℓ` odd and `> 0` ⇒ there are `n` and `Δ` with `nℓ = vν`, `Δ > 0`, `Δ ∣ ℓⁿ`, `n = 2h`, `Δ ≡ (-1)^h (mod 4)` |
| `Parity.centred_lattice_mod4` | "in particular" | if moreover every prime factor of `ℓ` is `≡ 1 (mod 4)` then `4 ∣ n` |
| `Parity.centred_sq`, `Parity.srg_param` (`SRG.lean`) | §2 | from Mathlib's `SimpleGraph.IsSRGWith v k λ μ`: `G = b(A-ρI)+cJ` satisfies `G² = b(θ-ρ)·G` whenever `ρ+θ = λ-μ`, `ρθ = μ-k`, `cv = -b(k-ρ)` (the identity `(k-ρ)(k-θ) = μv` is derived from `(A·A)·J = A·(A·J)`) |
| `Parity.srg_parity`, `Parity.srg_parity_mod4` | Cor. 4.1 (general `b`) | the corollary for any integers `b, c` with `cv = -b(k-ρ)` |
| `Parity.srg_parity_paper` | **Cor. 4.1 verbatim** | `a = v/gcd(v,k-ρ)`, `b = a·sgn(θ-ρ)`, `c = -b(k-ρ)/v`, `ν = c-bρ`, `ℓ = a|θ-ρ|`; `ν` even, `ℓ` odd ⇒ `n` even and `(-1)^{n/2} ≡ Δ (mod 4)` for a positive `Δ` whose prime factors divide `ℓ` |
| `Parity.no_srg_169_42_5_12` | §5.1 | `¬ Γ.IsSRGWith 169 42 5 12` for every finite simple graph `Γ` |
| `Parity.no_srg_NL` | Cor. 4.2 | `q = p^e`, `p ≡ 1 (mod 4)` prime, `m` odd ⇒ no graph is `IsSRGWith (q²) (m(q+1)) (m²+3m-q) (m(m+1))` |

The two non-existence theorems are unconditional: their only input is Mathlib's definition
`SimpleGraph.IsSRGWith`. Nothing (eigenvalues, multiplicities, Gram identity, lattice determinant)
is taken as a hypothesis.

## How the formal proof is organised

* **(F5)** by induction on the size: a row has an odd off-diagonal entry `G i j`; the plane
  `P = G[{i,j}]` has `det P = G_ii G_jj - G_ij² ≡ -1 (mod 4)`; the *integral* Schur complement
  `D'' = det P · D - C·adj(P)·B` is symmetric with even diagonal and
  `(det P)^m det G = det P · det D''` (proved over `ℚ` with Mathlib's `det_fromBlocks₁₁`).
  This is the paper's 2-adic splitting, done with integers instead of `ℤ₂`.
* **Vertex lattice.** Realised as `N = G·ℤ^V ⊆ ℤ^V` with form `(u·w)/ℓ` (isometric to the span of
  the vertex vectors, since `G² = ℓG`). Mathlib's `Submodule.basisOfPid` gives a `ℤ`-basis of rank
  `r`; with `G = BR`, `B = GX`, the basis Gram matrix is `G0 = XᵀGX` and `(RRᵀ)G0 = ℓI` — this is
  `ℓL^# ⊆ L` — so `det G0 ∣ ℓ^r`, and `det G0 > 0` because `det(RRᵀ) ≥ 0`.
* **Rank without spectral theory.** `trace G = trace(BR) = trace(RB) = ℓr`, so `r = vν/ℓ`.

## Differences from the paper's text (none is an error)

1. The paper's `n` is the multiplicity of `θ`; the Lean `n` is defined by `nℓ = vν` (it is the rank
   of the vertex lattice, computed by the trace). They agree (`G/ℓ` is the projection onto `E_θ`),
   but this identification is **not** formalised — it is not needed for any conclusion.
2. The sign of `det L` matters (`-13^j ≡ -1 (mod 4)` would *not* contradict (F5) at `n = 126`).
   The paper uses `det L > 0` implicitly (positive definite Gram); Lean proves it via `det(RRᵀ) ≥ 0`.
3. `srg_parity` accepts any `b` with `c = -b(k-ρ)/v` integral, not only the paper's minimal
   `a = v/gcd(v,k-ρ)`; `srg_parity_paper` is the paper's exact statement, derived from it.
4. Cor. 4.2 is proved without passing to the complement: `ρ = r = m`, `θ = s = m-q`, `b = -q`,
   `c = m` (i.e. `G = q(mI-A)+mJ`, the "other centred representation" of §5.1) gives `ν = m(q+1)`,
   `ℓ = q²`, `n = m(q+1) ≡ 2 (mod 4)` for every odd `m`, whatever `p ∣ m` or `p ∣ m+1`.
   The side condition `1 ≤ m ≤ q-2` is not needed for the non-existence statement.

## Build



```
lake exe cache get        # download the Mathlib build cache
lake build                # builds Parity (EvenLattice, Centred, SRG)
lake env lean Axioms.lean # prints the axioms of every main theorem
```

Clean build of the three files: ~2 min on 2 cores (`EvenLattice` ~20 s, `Centred` ~20 s,
`SRG` ~40 s, plus Mathlib import).
