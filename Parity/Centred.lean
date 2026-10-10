import Parity.EvenLattice

/-!
# The vertex lattice of a centred representation

Let `G` be a symmetric `V × V` integer matrix with constant even diagonal `ν` and
`G * G = ℓ • G` with `ℓ` odd and positive (for an srg, `G = b(A - ρI) + cJ`, see `Parity.SRG`).

The vertex lattice is realised as `N = G·ℤ^V ⊆ ℤ^V` (the `ℤ`-span of the columns of `G`) with
the form `⟨u, w⟩ = (u ⬝ w)/ℓ`; on the column `G e_i` this is `G i i`, so this is the lattice
spanned by vertex vectors with Gram matrix `G`. We take a `ℤ`-basis of `N` (Mathlib's
`Submodule.basisOfPid`, `N` is free of some rank `r`), write `B` for the basis matrix,
`R` for the coordinates of the columns of `G` (`G = B R`) and `X` with `B = G X`;
the Gram matrix of the basis is `G0 = Xᵀ G X` (integral, symmetric, even diagonal) and
`(R Rᵀ) G0 = ℓ • 1` (this is `ℓ L^# ⊆ L`), so `det G0 ∣ ℓ^r`, and `det G0 > 0`
because `det (R Rᵀ) ≥ 0`. Finally `trace G = trace (B R) = trace (R B) = ℓ r`, so
`r = v ν / ℓ`: the rank comes out of the trace, no spectral theory is needed.
Applying (F5) to `G0` gives the parity corollary.
-/

open Matrix

namespace Parity

/-- `∑_{i∈s} ∑_{j∈s} f i j` is even when `f` is symmetric with even diagonal. -/
lemma even_double_sum {ι : Type*} [DecidableEq ι] (f : ι → ι → ℤ) (hs : ∀ i j, f i j = f j i)
    (hd : ∀ i, Even (f i i)) (s : Finset ι) : Even (∑ i ∈ s, ∑ j ∈ s, f i j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
    have h1 : ∑ i ∈ s, f i a = ∑ i ∈ s, f a i := Finset.sum_congr rfl (fun i _ => hs i a)
    rw [h1]
    have h2 : f a a + ∑ j ∈ s, f a j + (∑ i ∈ s, f a i + ∑ i ∈ s, ∑ j ∈ s, f i j)
        = f a a + 2 * ∑ j ∈ s, f a j + ∑ i ∈ s, ∑ j ∈ s, f i j := by ring
    rw [h2]
    exact ((hd a).add (even_two_mul _)).add ih

/-- The vertex-lattice theorem for a centred representation. -/
theorem centred_lattice {V : Type*} [Fintype V] [DecidableEq V] (G : Matrix V V ℤ) (ℓ ν : ℤ)
    (hS : G.IsSymm) (hdiag : ∀ i, G i i = ν) (hν : Even ν) (hsq : G * G = ℓ • G)
    (hℓ : Odd ℓ) (hℓpos : 0 < ℓ) :
    ∃ (n : ℕ) (Δ : ℤ), (n : ℤ) * ℓ = Fintype.card V * ν ∧ 0 < Δ ∧ Δ ∣ ℓ ^ n ∧
      ∃ h : ℕ, n = 2 * h ∧ Δ ≡ (-1) ^ h [ZMOD 4] := by
  classical
  let N : Submodule ℤ (V → ℤ) := LinearMap.range (Matrix.mulVecLin G)
  obtain ⟨r, bN⟩ := Submodule.basisOfPid (Pi.basisFun ℤ V) N
  let B : Matrix V (Fin r) ℤ := of fun i a => (bN a : V → ℤ) i
  have hmem : ∀ a, ∃ x : V → ℤ, G *ᵥ x = (bN a : V → ℤ) := fun a => by
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (bN a).2
    exact ⟨x, by simpa using hx⟩
  choose x hx using hmem
  let X : Matrix V (Fin r) ℤ := of fun i a => x a i
  have hcol : ∀ j, (fun i => G i j) ∈ N := fun j =>
    ⟨Pi.single j 1, by rw [mulVecLin_apply, mulVec_single_one]; rfl⟩
  let R : Matrix (Fin r) V ℤ := of fun a j => bN.repr ⟨fun i => G i j, hcol j⟩ a
  -- `G = B R`
  have hGBR : G = B * R := by
    ext i j
    have := congrArg (fun y : N => (y : V → ℤ) i) (bN.sum_repr ⟨fun i => G i j, hcol j⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at this
    rw [mul_apply, ← this]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  -- `B = G X`
  have hBGX : B = G * X := by
    ext i a
    simp only [B, X, mul_apply, of_apply]
    rw [← hx a]
    rfl
  -- `B` is injective
  have hBinj : ∀ w : Fin r → ℤ, B *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hli := Fintype.linearIndependent_iff.mp bN.linearIndependent w
    funext a
    apply hli
    apply Subtype.ext
    funext i
    have := congrFun hw i
    simp only [mulVec, dotProduct, B, of_apply, Pi.zero_apply] at this
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  have hBcancel : ∀ M M' : Matrix (Fin r) (Fin r) ℤ, B * M = B * M' → M = M' := by
    intro M M' h
    ext a b
    have h0 := hBinj (fun c => M c b - M' c b) (by
      funext i
      have := congrFun (congrFun h i) b
      simp only [mul_apply] at this
      simp only [mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, Pi.zero_apply]
      rw [this, sub_self])
    have := congrFun h0 a
    simpa [sub_eq_zero] using this
  -- `R B = ℓ • 1`
  have hRB : R * B = ℓ • (1 : Matrix (Fin r) (Fin r) ℤ) := by
    apply hBcancel
    calc B * (R * B) = (B * R) * B := by rw [Matrix.mul_assoc]
      _ = G * B := by rw [← hGBR]
      _ = G * (G * X) := by rw [← hBGX]
      _ = ℓ • (G * X) := by rw [← Matrix.mul_assoc, hsq, Matrix.smul_mul]
      _ = B * (ℓ • (1 : Matrix (Fin r) (Fin r) ℤ)) := by rw [← hBGX, Matrix.mul_smul, Matrix.mul_one]
  -- the Gram matrix of the basis
  let G0 : Matrix (Fin r) (Fin r) ℤ := Xᵀ * G * X
  have hBT : Bᵀ = Xᵀ * G := by rw [hBGX, transpose_mul, hS.eq]
  have hG0 : G0 = Bᵀ * X := by rw [hBT]
  have hRG0 : Rᵀ * G0 = B := by
    rw [hG0, ← Matrix.mul_assoc, ← transpose_mul, ← hGBR, hS.eq, ← hBGX]
  have hkey : (R * Rᵀ) * G0 = ℓ • (1 : Matrix (Fin r) (Fin r) ℤ) := by
    rw [Matrix.mul_assoc, hRG0, hRB]
  have hdet : (R * Rᵀ).det * G0.det = ℓ ^ r := by
    rw [← det_mul, hkey, det_smul, det_one, Fintype.card_fin, mul_one]
  have htrace : (r : ℤ) * ℓ = Fintype.card V * ν := by
    have h1 : G.trace = Fintype.card V * ν := by
      simp [Matrix.trace, hdiag]
    have h2 : G.trace = ℓ * r := by
      rw [hGBR, trace_mul_comm, hRB, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    rw [← h1, h2, mul_comm]
  -- `det (R Rᵀ) ≥ 0`
  have hpsd : 0 ≤ (R * Rᵀ).det := by
    let f := Int.castRingHom ℝ
    have h := (posSemidef_self_mul_conjTranspose (R.map f)).det_nonneg
    rw [conjTranspose_eq_transpose_of_trivial, ← transpose_map, ← Matrix.map_mul,
      ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
    have h' : (0 : ℝ) ≤ ((R * Rᵀ).det : ℝ) := h
    exact_mod_cast h'
  -- `G0` is symmetric with even diagonal
  have hG0S : G0.IsSymm := by
    show (Xᵀ * G * X)ᵀ = Xᵀ * G * X
    rw [transpose_mul, transpose_mul, transpose_transpose, hS.eq, Matrix.mul_assoc]
  have hG0E : ∀ a, Even (G0 a a) := by
    intro a
    have : G0 a a = ∑ j, ∑ i, X i a * G i j * X j a := by
      simp only [G0, mul_apply, transpose_apply, Finset.sum_mul]
    rw [this]
    apply even_double_sum (fun j i => X i a * G i j * X j a)
    · intro j i
      show X i a * G i j * X j a = X j a * G j i * X i a
      rw [hS.apply i j]
      ring
    · intro i
      rw [hdiag]
      exact (hν.mul_left _).mul_right _
  have hpow : 0 < ℓ ^ r := pow_pos hℓpos r
  have hΔpos : 0 < G0.det := by
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonneg_of_nonpos hpsd hneg
    rw [hdet] at this
    exact absurd hpow (not_lt.mpr this)
  have hΔodd : Odd G0.det := by
    have : Odd ((R * Rᵀ).det * G0.det) := hdet ▸ hℓ.pow
    exact (Int.odd_mul.mp this).2
  obtain ⟨h, hr, hmod⟩ := even_det_odd G0 hG0S hG0E hΔodd
  rw [Fintype.card_fin] at hr
  exact ⟨r, G0.det, htrace, hΔpos, ⟨(R * Rᵀ).det, by rw [← hdet]; ring⟩, h, hr, hmod⟩

/-- If all prime factors of a nonzero natural number are `≡ 1 (mod 4)`, so is the number. -/
lemma mod_four_of_prime_factors : ∀ (d : ℕ), d ≠ 0 →
    (∀ p : ℕ, p.Prime → p ∣ d → p % 4 = 1) → d % 4 = 1 := by
  intro d
  induction d using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; rfl
  | prime p hp => intro _ h; exact h p hp dvd_rfl
  | mul a b ha hb =>
    intro hab h
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hab
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hab
    have h1 := ha ha0 (fun p hp hpa => h p hp (dvd_mul_of_dvd_left hpa b))
    have h2 := hb hb0 (fun p hp hpb => h p hp (dvd_mul_of_dvd_right hpb a))
    rw [Nat.mul_mod, h1, h2]

/-- The "in particular" clause: if every prime factor of `ℓ` is `≡ 1 (mod 4)`, then `4 ∣ n`. -/
theorem centred_lattice_mod4 {V : Type*} [Fintype V] [DecidableEq V] (G : Matrix V V ℤ)
    (ℓ ν : ℤ) (hS : G.IsSymm) (hdiag : ∀ i, G i i = ν) (hν : Even ν) (hsq : G * G = ℓ • G)
    (hℓ : Odd ℓ) (hℓpos : 0 < ℓ) (hprimes : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ ℓ → p % 4 = 1) :
    ∃ n : ℕ, (n : ℤ) * ℓ = Fintype.card V * ν ∧ 4 ∣ n := by
  obtain ⟨n, Δ, hn, hΔ, hdvd, h, rfl, hmod⟩ := centred_lattice G ℓ ν hS hdiag hν hsq hℓ hℓpos
  refine ⟨2 * h, hn, ?_⟩
  have hΔ1 : Δ ≡ 1 [ZMOD 4] := by
    have hd := mod_four_of_prime_factors Δ.toNat (by omega) (fun p hp hpd => by
      apply hprimes p hp
      have h1 : (p : ℤ) ∣ Δ := by
        have := Int.natCast_dvd_natCast.mpr hpd
        rwa [Int.toNat_of_nonneg hΔ.le] at this
      exact Int.Prime.dvd_pow' hp (h1.trans hdvd))
    have : (Δ.toNat : ℤ) = Δ := Int.toNat_of_nonneg hΔ.le
    rw [← this]
    show ((Δ.toNat : ℕ) : ℤ) % 4 = 1 % 4
    omega
  rcases Nat.even_or_odd h with he | ho
  · obtain ⟨t, rfl⟩ := he
    exact ⟨t, by ring⟩
  · exfalso
    rw [ho.neg_one_pow] at hmod
    have := hmod.symm.trans hΔ1
    revert this
    decide

end Parity
