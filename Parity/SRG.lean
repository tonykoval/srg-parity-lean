import Parity.Centred

/-!
# The parity corollary for strongly regular graphs (Cor. 4.1, Cor. 4.2, srg(169,42,5,12))

From Mathlib's `SimpleGraph.IsSRGWith v k λ μ` only (no spectral data assumed), with integers
`ρ, θ` satisfying `ρ + θ = λ - μ`, `ρ θ = μ - k` (the restricted eigenvalues; we never need that
they *are* eigenvalues) and integers `b, c` with `c v = -b (k - ρ)`, the centred matrix
`G = b(A - ρI) + cJ` satisfies `G² = ℓ G` with `ℓ = b(θ - ρ)`; its diagonal is `ν = c - bρ`.
`Parity.centred_lattice` then gives the parity corollary, with `n = vν/ℓ`.
-/

open Matrix SimpleGraph

namespace Parity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The all-ones matrix. -/
def allOnes (V : Type*) : Matrix V V ℤ := of fun _ _ => 1

/-- The centred matrix `b(A - ρI) + cJ`. -/
def centredMatrix (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (b ρ c : ℤ) : Matrix V V ℤ :=
  b • (Γ.adjMatrix ℤ - ρ • (1 : Matrix V V ℤ)) + c • allOnes V

section
variable (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {v k l m : ℕ}

lemma srg_A2 (h : Γ.IsSRGWith v k l m) :
    Γ.adjMatrix ℤ * Γ.adjMatrix ℤ = (k : ℤ) • (1 : Matrix V V ℤ) + (l : ℤ) • Γ.adjMatrix ℤ
      + (m : ℤ) • (allOnes V - 1 - Γ.adjMatrix ℤ) := by
  have h1 := h.matrix_eq (α := ℤ)
  have hc : Γᶜ.adjMatrix ℤ = allOnes V - 1 - Γ.adjMatrix ℤ := by
    have := Γ.one_add_adjMatrix_add_compl_adjMatrix_eq_of_one (α := ℤ)
    rw [compl_adjMatrix_eq_adjMatrix_compl] at this
    show Γᶜ.adjMatrix ℤ = (of 1 : Matrix V V ℤ) - 1 - Γ.adjMatrix ℤ
    rw [← this]
    abel
  rw [sq, hc] at h1
  rw [h1, natCast_zsmul, natCast_zsmul, natCast_zsmul]

lemma srg_AJ (h : Γ.IsSRGWith v k l m) :
    Γ.adjMatrix ℤ * allOnes V = (k : ℤ) • allOnes V := by
  ext i j
  simp [allOnes, adjMatrix_mul_apply, h.regular i]

lemma srg_JA (h : Γ.IsSRGWith v k l m) :
    allOnes V * Γ.adjMatrix ℤ = (k : ℤ) • allOnes V := by
  ext i j
  simp [allOnes, mul_adjMatrix_apply, h.regular j]

lemma srg_JJ (h : Γ.IsSRGWith v k l m) :
    allOnes V * allOnes V = (v : ℤ) • allOnes V := by
  ext i j
  simp [allOnes, mul_apply, h.card]

/-- The counting identity `k² = k + λk + μ(v - 1 - k)`, read off `(A·A)·J = A·(A·J)`. -/
lemma srg_param (h : Γ.IsSRGWith v k l m) (hv : 0 < v) :
    (k : ℤ) ^ 2 = k + l * k + m * (v - 1 - k) := by
  obtain ⟨i⟩ : Nonempty V := by
    rw [← Fintype.card_pos_iff, h.card]; exact hv
  have e : (Γ.adjMatrix ℤ * Γ.adjMatrix ℤ) * allOnes V
      = Γ.adjMatrix ℤ * (Γ.adjMatrix ℤ * allOnes V) := Matrix.mul_assoc _ _ _
  rw [srg_A2 Γ h, srg_AJ Γ h, Matrix.mul_smul, srg_AJ Γ h] at e
  simp only [add_mul, sub_mul, Matrix.smul_mul, Matrix.one_mul, srg_AJ Γ h, srg_JJ Γ h] at e
  have := congrFun (congrFun e i) i
  simp [allOnes] at this
  linear_combination -this

/-- `G² = ℓ G` for the centred matrix. -/
theorem centred_sq (h : Γ.IsSRGWith v k l m) (hv : 0 < v) (ρ θ b c : ℤ)
    (h1 : ρ + θ = l - m) (h2 : ρ * θ = m - k) (h3 : c * v = -b * (k - ρ)) :
    centredMatrix Γ b ρ c * centredMatrix Γ b ρ c
      = (b * (θ - ρ)) • centredMatrix Γ b ρ c := by
  have hpar := srg_param Γ h hv
  have h4 : ((k : ℤ) - ρ) * (k - θ) = m * v := by
    linear_combination hpar - (k : ℤ) * h1 + h2
  set A := Γ.adjMatrix ℤ
  set J := allOnes V
  have hA2 := srg_A2 Γ h
  have hAJ := srg_AJ Γ h
  have hJA := srg_JA Γ h
  have hJJ := srg_JJ Γ h
  have e1 : centredMatrix Γ b ρ c * centredMatrix Γ b ρ c
      = (b * b) • (A * A) + (b * c) • (A * J) + (c * b) • (J * A) + (c * c) • (J * J)
        - (2 * b * b * ρ) • A - (b * c * ρ) • J - (c * b * ρ) • J
        + (b * b * ρ * ρ) • (1 : Matrix V V ℤ) := by
    simp only [centredMatrix, add_mul, mul_add, sub_mul, mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  rw [e1, hA2, hAJ, hJA, hJJ]
  set α : ℤ := b * b * (l - m - 2 * ρ) - b * (θ - ρ) * b
  set β : ℤ := b * b * (k - m + ρ * ρ) + b * (θ - ρ) * b * ρ
  set γ : ℤ := b * b * m + 2 * b * c * (k - ρ) + c * c * v - b * (θ - ρ) * c
  have hα : α = 0 := by simp only [α]; linear_combination (-b * b) * h1
  have hβ : β = 0 := by simp only [β]; linear_combination (b * b) * h2
  have hγ : γ = 0 := by
    have hvγ : (v : ℤ) * γ = 0 := by
      simp only [γ]
      linear_combination (c * v + b * (k - θ)) * h3 - b ^ 2 * h4
    exact (mul_eq_zero.mp hvγ).resolve_left (by exact_mod_cast hv.ne')
  rw [← sub_eq_zero]
  have e2 : (b * b) • ((k : ℤ) • (1 : Matrix V V ℤ) + (l : ℤ) • A + (m : ℤ) • (J - 1 - A))
        + (b * c) • ((k : ℤ) • J) + (c * b) • ((k : ℤ) • J) + (c * c) • ((v : ℤ) • J)
        - (2 * b * b * ρ) • A - (b * c * ρ) • J - (c * b * ρ) • J
        + (b * b * ρ * ρ) • (1 : Matrix V V ℤ)
        - (b * (θ - ρ)) • centredMatrix Γ b ρ c
      = α • A + β • (1 : Matrix V V ℤ) + γ • J := by
    simp only [centredMatrix, α, β, γ]
    module
  rw [e2, hα, hβ, hγ]
  simp

lemma centred_symm (b ρ c : ℤ) : (centredMatrix Γ b ρ c).IsSymm := by
  unfold centredMatrix
  refine IsSymm.add (IsSymm.smul (IsSymm.sub (isSymm_adjMatrix Γ) (isSymm_one.smul ρ)) b)
    (IsSymm.smul (IsSymm.ext fun _ _ => rfl) c)

lemma centred_diag (b ρ c : ℤ) (i : V) : centredMatrix Γ b ρ c i i = c - b * ρ := by
  rw [centredMatrix, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply,
    one_apply_eq, adjMatrix_apply]
  simp [allOnes]
  ring

/-- **Corollary 4.1 (parity corollary), general form.** For an `srg(v,k,λ,μ)` and integers
`ρ, θ, b, c` with `ρ + θ = λ - μ`, `ρθ = μ - k`, `cv = -b(k-ρ)`, put `ν = c - bρ` and
`ℓ = b(θ - ρ)`. If `ν` is even and `ℓ` is odd and positive, then `n := vν/ℓ` is an even
natural number `2h`, and some positive integer `Δ ∣ ℓ^n` (the determinant of the vertex
lattice) satisfies `Δ ≡ (-1)^h (mod 4)`. -/
theorem srg_parity (h : Γ.IsSRGWith v k l m) (hv : 0 < v) (ρ θ b c : ℤ)
    (h1 : ρ + θ = l - m) (h2 : ρ * θ = m - k) (h3 : c * v = -b * (k - ρ))
    (hν : Even (c - b * ρ)) (hℓ : Odd (b * (θ - ρ))) (hℓpos : 0 < b * (θ - ρ)) :
    ∃ (n : ℕ) (Δ : ℤ), (n : ℤ) * (b * (θ - ρ)) = v * (c - b * ρ) ∧ 0 < Δ ∧
      Δ ∣ (b * (θ - ρ)) ^ n ∧ ∃ h : ℕ, n = 2 * h ∧ Δ ≡ (-1) ^ h [ZMOD 4] := by
  have := centred_lattice (centredMatrix Γ b ρ c) (b * (θ - ρ)) (c - b * ρ)
    (centred_symm Γ b ρ c) (centred_diag Γ b ρ c) hν (centred_sq Γ h hv ρ θ b c h1 h2 h3)
    hℓ hℓpos
  rwa [h.card] at this

/-- **Corollary 4.1, "in particular" clause**: if moreover every prime factor of `ℓ` is
`≡ 1 (mod 4)`, then `4 ∣ n`. -/
theorem srg_parity_mod4 (h : Γ.IsSRGWith v k l m) (hv : 0 < v) (ρ θ b c : ℤ)
    (h1 : ρ + θ = l - m) (h2 : ρ * θ = m - k) (h3 : c * v = -b * (k - ρ))
    (hν : Even (c - b * ρ)) (hℓ : Odd (b * (θ - ρ))) (hℓpos : 0 < b * (θ - ρ))
    (hprimes : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b * (θ - ρ) → p % 4 = 1) :
    ∃ n : ℕ, (n : ℤ) * (b * (θ - ρ)) = v * (c - b * ρ) ∧ 4 ∣ n := by
  have := centred_lattice_mod4 (centredMatrix Γ b ρ c) (b * (θ - ρ)) (c - b * ρ)
    (centred_symm Γ b ρ c) (centred_diag Γ b ρ c) hν (centred_sq Γ h hv ρ θ b c h1 h2 h3)
    hℓ hℓpos hprimes
  rwa [h.card] at this

lemma sign_mul_self_eq_abs (x : ℤ) : Int.sign x * x = |x| := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Int.sign_eq_neg_one_of_neg hx, abs_of_neg hx]; ring
  · subst hx; simp
  · rw [Int.sign_eq_one_of_pos hx, abs_of_pos hx]; ring

/-- **Corollary 4.1 exactly as stated in the paper.** `a = v / gcd(v, k-ρ)`,
`b = a·sgn(θ-ρ)`, `c = -b(k-ρ)/v`, `ν = c - bρ`, `ℓ = a|θ-ρ|`. If `ν` is even and `ℓ` is odd,
then `n` is even and `(-1)^(n/2) ≡ Δ (mod 4)` for some positive integer `Δ` all of whose prime
factors divide `ℓ`. Here `n` is *defined* by `n ℓ = v ν` (the paper's `n` is the multiplicity
of `θ`; that the two agree is the standard spectral fact `rank G = mult θ`, which the proof
does not need). -/
theorem srg_parity_paper (h : Γ.IsSRGWith v k l m) (hv : 0 < v) (ρ θ : ℤ) (hρθ : ρ ≠ θ)
    (h1 : ρ + θ = l - m) (h2 : ρ * θ = m - k) (a b c ν ℓ : ℤ)
    (ha : a = v / (Int.gcd v (k - ρ) : ℤ)) (hb : b = a * Int.sign (θ - ρ))
    (hc : c = -(b * (k - ρ)) / v) (hνdef : ν = c - b * ρ) (hℓdef : ℓ = a * |θ - ρ|)
    (hν : Even ν) (hℓ : Odd ℓ) :
    ∃ n : ℕ, (n : ℤ) * ℓ = v * ν ∧ Even n ∧
      ∃ Δ : ℤ, 0 < Δ ∧ (∀ p : ℕ, p.Prime → (p : ℤ) ∣ Δ → (p : ℤ) ∣ ℓ) ∧
        (-1) ^ (n / 2) ≡ Δ [ZMOD 4] := by
  set g : ℕ := Int.gcd v (k - ρ) with hg
  have hv0 : (v : ℤ) ≠ 0 := by exact_mod_cast hv.ne'
  have hgpos : 0 < (g : ℤ) := by exact_mod_cast Int.gcd_pos_of_ne_zero_left _ hv0
  obtain ⟨v', hv'⟩ : (g : ℤ) ∣ v := Int.gcd_dvd_left _ _
  obtain ⟨t, ht⟩ : (g : ℤ) ∣ (k : ℤ) - ρ := Int.gcd_dvd_right _ _
  have ha' : a = v' := by
    rw [ha, hv', Int.mul_ediv_cancel_left _ hgpos.ne']
  have hbk : b * (k - ρ) = v * (Int.sign (θ - ρ) * t) := by
    rw [hb, ht, ha', hv']; ring
  have hc' : c = -(Int.sign (θ - ρ) * t) := by
    rw [hc, hbk, ← mul_neg, Int.mul_ediv_cancel_left _ hv0]
  have h3 : c * v = -b * (k - ρ) := by
    rw [neg_mul, hbk, hc']; ring
  have hℓb : ℓ = b * (θ - ρ) := by
    rw [hℓdef, hb, mul_assoc, sign_mul_self_eq_abs]
  have hapos : 0 < a := by
    rw [ha']
    have : 0 < (g : ℤ) * v' := by rw [← hv']; exact_mod_cast hv
    exact pos_of_mul_pos_right this hgpos.le
  have hℓpos : 0 < b * (θ - ρ) := by
    rw [← hℓb, hℓdef]
    exact mul_pos hapos (abs_pos.mpr (sub_ne_zero.mpr hρθ.symm))
  obtain ⟨n, Δ, hn, hΔ, hdvd, hh, rfl, hmod⟩ := srg_parity Γ h hv ρ θ b c h1 h2 h3
    (hνdef ▸ hν) (hℓb ▸ hℓ) hℓpos
  refine ⟨2 * hh, by rw [hℓb, hνdef]; exact hn, even_two_mul _, Δ, hΔ, ?_, ?_⟩
  · intro p hp hpΔ
    rw [hℓb]
    exact Int.Prime.dvd_pow' hp (hpΔ.trans hdvd)
  · rw [Nat.mul_div_cancel_left _ (by norm_num)]
    exact hmod.symm

end

/-- **Worked example (§5.1): there is no `srg(169,42,5,12)`.**
`ρ = s = -10`, `θ = r = 3`, `G = 13(A + 10I) - 4J`, `ν = 126`, `ℓ = 169 = 13²`, `n = 126`. -/
theorem no_srg_169_42_5_12 (Γ : SimpleGraph V) [DecidableRel Γ.Adj] :
    ¬ Γ.IsSRGWith 169 42 5 12 := by
  intro h
  obtain ⟨n, hn, h4⟩ := srg_parity_mod4 Γ h (by norm_num) (-10) 3 13 (-4)
    (by norm_num) (by norm_num) (by norm_num) ⟨63, by norm_num⟩ ⟨84, by norm_num⟩
    (by norm_num) (fun p hp hpd => by
      have h169 : p ∣ 13 ^ 2 := by
        have : (p : ℤ) ∣ ((13 ^ 2 : ℕ) : ℤ) := by norm_num at hpd ⊢; exact hpd
        exact Int.natCast_dvd_natCast.mp this
      have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h169)
      subst this; norm_num)
  norm_num at hn
  omega

/-- **Corollary 4.2 (negative-Latin-square parameters).** Let `q = p^e` with `p ≡ 1 (mod 4)`
prime and `m` odd. There is no strongly regular graph with the parameters
`(q², m(q+1), -q + m² + 3m, m(m+1))` of `NL_m(q)`.
(Proof: the centred representation for `ρ = r = m`, `θ = s = m - q`, `b = -q`, `c = m`, i.e.
`G = q(mI - A) + mJ`, `ν = m(q+1)`, `ℓ = q²`, `n = m(q+1) ≡ 2 (mod 4)`; this needs no passage
to the complement.) -/
theorem no_srg_NL (Γ : SimpleGraph V) [DecidableRel Γ.Adj] (p e m lam : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 1) (hm : Odd m) (hlam : (lam : ℤ) = m ^ 2 + 3 * m - (p ^ e : ℕ)) :
    ¬ Γ.IsSRGWith ((p ^ e) ^ 2) (m * (p ^ e + 1)) lam (m * (m + 1)) := by
  intro h
  set q := p ^ e with hqdef
  have hq0 : 0 < q := pow_pos hp.pos e
  have hq4 : q % 4 = 1 := by rw [hqdef, Nat.pow_mod, hp4]; simp
  have hqodd : Odd (q : ℤ) := by
    have : q % 2 = 1 := by omega
    exact Int.odd_iff.mpr (by exact_mod_cast this)
  obtain ⟨n, hn, h4⟩ := srg_parity_mod4 Γ h (by positivity) (m : ℤ) ((m : ℤ) - q) (-(q : ℤ))
    (m : ℤ)
    (by push_cast; rw [hlam]; ring) (by push_cast; ring) (by push_cast; ring)
    (by
      have : (m : ℤ) - -(q : ℤ) * m = m * (q + 1) := by ring
      rw [this]
      exact Even.mul_left (hqodd.add_one) _)
    (by
      have : -(q : ℤ) * ((m : ℤ) - q - m) = q ^ 2 := by ring
      rw [this]; exact hqodd.pow)
    (by
      have : -(q : ℤ) * ((m : ℤ) - q - m) = q ^ 2 := by ring
      rw [this]; positivity)
    (fun p' hp' hpd => by
      have : -(q : ℤ) * ((m : ℤ) - q - m) = ((p ^ (2 * e) : ℕ) : ℤ) := by
        rw [hqdef]; push_cast; ring
      rw [this] at hpd
      have h1 := Int.natCast_dvd_natCast.mp hpd
      have := (Nat.prime_dvd_prime_iff_eq hp' hp).mp (hp'.dvd_of_dvd_pow h1)
      subst this; exact hp4)
  have hn' : (n : ℤ) = m * (q + 1) := by
    have e1 : ((q : ℤ) ^ 2) * n = ((q : ℤ) ^ 2) * (m * (q + 1)) := by
      push_cast at hn
      linear_combination hn
    exact mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hq0.ne')) e1
  have hn'' : n = m * (q + 1) := by exact_mod_cast hn'
  have hmod : m * (q + 1) % 4 = 2 := by
    have hm2 : m % 2 = 1 := Nat.odd_iff.mp hm
    rw [Nat.mul_mod, Nat.add_mod, hq4]
    have : m % 4 = 1 ∨ m % 4 = 3 := by omega
    rcases this with h' | h' <;> simp [h']
  omega

end Parity
