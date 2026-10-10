import Mathlib

/-!
# (F5): even lattices of odd determinant

If `G` is an `n × n` symmetric integer matrix with even diagonal (the Gram matrix of an even
lattice) and `det G` is odd, then `n` is even and `det G ≡ (-1)^(n/2) (mod 4)`.

Proof (as in the paper, 2-adic splitting of a hyperbolic plane, done over `ℤ`/`ℚ`):
a row of `G` must contain an odd entry `G i j` (`j ≠ i`, the diagonal being even); the plane
`P = G[{i,j},{i,j}]` has `det P = G i i * G j j - (G i j)^2 ≡ -1 (mod 4)`; the integral
Schur complement `D'' = det P • D - C * adj P * B` is again symmetric with even diagonal and
satisfies `(det P)^m * det G = det P * det D''` (`m = n - 2`); induct.
-/

open Matrix

namespace Parity

section F5

variable {ι : Type*} [DecidableEq ι]

/-- The reindexing `Fin 2 ⊕ {x // x ≠ i ∧ x ≠ j} ≃ ι` sending `inl 0 ↦ i`, `inl 1 ↦ j`. -/
def pairEquiv (i j : ι) (hij : i ≠ j) : Fin 2 ⊕ {x : ι // x ≠ i ∧ x ≠ j} ≃ ι where
  toFun := Sum.elim (fun a => if a = 0 then i else j) Subtype.val
  invFun x := if hx : x = i then Sum.inl 0 else if hy : x = j then Sum.inl 1 else
    Sum.inr ⟨x, hx, hy⟩
  left_inv := by
    rintro (a | ⟨x, hx, hy⟩)
    · fin_cases a
      · simp
      · simp [hij.symm]
    · simp [hx, hy]
  right_inv := by
    intro x
    by_cases hx : x = i
    · simp [hx]
    · by_cases hy : x = j
      · subst hy; simp [hij.symm]
      · simp [hx, hy]

@[simp] lemma pairEquiv_inl0 (i j : ι) (h : i ≠ j) : pairEquiv i j h (Sum.inl 0) = i := by
  simp [pairEquiv]

@[simp] lemma pairEquiv_inl1 (i j : ι) (h : i ≠ j) : pairEquiv i j h (Sum.inl 1) = j := by
  simp [pairEquiv]

@[simp] lemma pairEquiv_inr (i j : ι) (h : i ≠ j) (x : {x : ι // x ≠ i ∧ x ≠ j}) :
    pairEquiv i j h (Sum.inr x) = x.1 := rfl

/-- An odd integer is `≡ -1 (mod 4)` after negating its square: `4ad - b^2 ≡ -1`. -/
lemma plane_det_mod4 (a d b : ℤ) (hb : Odd b) : (2 * a) * (2 * d) - b * b ≡ -1 [ZMOD 4] := by
  obtain ⟨t, rfl⟩ := hb
  rw [Int.modEq_iff_dvd]
  exact ⟨t ^ 2 + t - a * d, by ring⟩

/-- **(F5)**, Fintype form with an explicit cardinality. -/
theorem even_det_odd_aux : ∀ (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℤ), Fintype.card ι = N → G.IsSymm → (∀ i, Even (G i i)) → Odd G.det →
    ∃ h : ℕ, N = 2 * h ∧ G.det ≡ (-1) ^ h [ZMOD 4] := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro ι _ _ G hN hS hE hO
  have hS' : ∀ a b, G b a = G a b := fun a b => hS.apply a b
  match N, hN, ih with
  | 0, hN, _ =>
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hN
    exact ⟨0, rfl, by simp [det_isEmpty]⟩
  | 1, hN, _ =>
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hN
    haveI : Unique ι := ⟨⟨x⟩, hx⟩
    exfalso
    rw [det_unique] at hO
    exact (Int.not_even_iff_odd.mpr hO) (hE _)
  | m + 2, hN, ih =>
    obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    -- some entry of row `i` is odd
    have hrow : ∃ j, Odd (G i j) := by
      by_contra hcon
      push_neg at hcon
      have h0 : ((Int.castRingHom (ZMod 2)).mapMatrix G).det = 0 := by
        apply det_eq_zero_of_row_eq_zero i
        intro j
        simp only [RingHom.mapMatrix_apply, map_apply, eq_intCast]
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr
          (even_iff_two_dvd.mp (Int.not_odd_iff_even.mp (hcon j)))
      rw [← RingHom.map_det, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      exact (Int.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr (by exact_mod_cast h0))
    obtain ⟨j, hj⟩ := hrow
    have hij : i ≠ j := by
      rintro rfl
      exact (Int.not_even_iff_odd.mpr hj) (hE i)
    set κ := {x : ι // x ≠ i ∧ x ≠ j}
    set e := pairEquiv i j hij
    have hκ : Fintype.card κ = m := by
      have := Fintype.card_congr e
      rw [Fintype.card_sum, Fintype.card_fin, hN] at this
      have h2 : Fintype.card κ = Fintype.card {x : ι // x ≠ i ∧ x ≠ j} :=
        Fintype.card_congr (Equiv.refl _)
      omega
    -- blocks
    let P : Matrix (Fin 2) (Fin 2) ℤ := of fun a b => G (e (Sum.inl a)) (e (Sum.inl b))
    let B : Matrix (Fin 2) κ ℤ := of fun a k => G (e (Sum.inl a)) k.1
    let C : Matrix κ (Fin 2) ℤ := of fun k a => G k.1 (e (Sum.inl a))
    let D : Matrix κ κ ℤ := of fun k l => G k.1 l.1
    have hblk : G.submatrix e e = fromBlocks P B C D := by
      ext x y
      rcases x with a | k <;> rcases y with b | l <;> rfl
    set p := P.det with hpdef
    have hp : p = G i i * G j j - G i j * G i j := by
      rw [hpdef, det_fin_two]
      simp [P, e, hS' i j]
    have hp4 : p ≡ -1 [ZMOD 4] := by
      obtain ⟨a, ha⟩ := hE i
      obtain ⟨d, hd⟩ := hE j
      rw [hp, ha, hd, show a + a = 2 * a by ring, show d + d = 2 * d by ring]
      exact plane_det_mod4 a d _ hj
    have hpodd : Odd p := by
      have : (4 : ℤ) ∣ -1 - p := Int.ModEq.dvd hp4
      obtain ⟨t, ht⟩ := this
      exact ⟨-2 * t - 1, by linarith⟩
    -- the integral Schur complement
    let D'' : Matrix κ κ ℤ := p • D - C * adjugate P * B
    have hD : ∀ k l : κ, D'' k l = p * G k.1 l.1 -
        (G k.1 i * G j j * G i l.1 - G k.1 i * G i j * G j l.1
          - G k.1 j * G j i * G i l.1 + G k.1 j * G i i * G j l.1) := by
      intro k l
      simp [D'', D, C, B, P, e, mul_apply, Fin.sum_univ_two, adjugate_fin_two]
      ring
    have hDsym : D''.IsSymm := by
      refine IsSymm.ext fun k l => ?_
      rw [hD, hD]
      simp only [hS' k.1 l.1, hS' i l.1, hS' i k.1, hS' j l.1, hS' j k.1, hS' i j]
      ring
    have hDeven : ∀ k, Even (D'' k k) := by
      intro k
      rw [hD]
      simp only [hS' i k.1, hS' j k.1, hS' i j]
      have : p * G k.1 k.1 -
          (G i k.1 * G j j * G i k.1 - G i k.1 * G i j * G j k.1
            - G j k.1 * G i j * G i k.1 + G j k.1 * G i i * G j k.1)
          = p * G k.1 k.1 - (G j j * G i k.1 ^ 2 + G i i * G j k.1 ^ 2)
            + 2 * (G i j * G i k.1 * G j k.1) := by ring
      rw [this]
      exact ((hE k.1).mul_left p |>.sub
        (((hE j).mul_right _).add ((hE i).mul_right _))).add (even_two_mul _)
    -- the determinant identity `p^m * det G = p * det D''`, via the Schur complement over ℚ
    have key : p ^ m * G.det = p * D''.det := by
      let f := Int.castRingHom ℚ
      have hp0' : p ≠ 0 := by
        intro h
        have := Int.odd_iff.mp hpodd
        rw [h] at this
        norm_num at this
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp0'
      have hPdet : (P.map f).det = (p : ℚ) := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
      haveI : Invertible (P.map f) :=
        invertibleOfIsUnitDet _ (by rw [hPdet]; exact isUnit_iff_ne_zero.mpr hp0)
      have hG : (G.map f).det = (G.det : ℚ) := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
      have hD'' : (D''.map f).det = (D''.det : ℚ) := by
        rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
      have hsub : ((G.submatrix e e).map f).det = (G.map f).det := by
        rw [← submatrix_map, det_submatrix_equiv_self]
      have hadj : (adjugate P).map f = adjugate (P.map f) := by
        rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate]; rfl
      have hinv : ⅟(P.map f) = (p : ℚ)⁻¹ • adjugate (P.map f) := by
        rw [invOf_eq_nonsing_inv, inv_def, hPdet, Ring.inverse_eq_inv']
      have hschur : D.map f - C.map f * ⅟(P.map f) * B.map f = (p : ℚ)⁻¹ • D''.map f := by
        rw [hinv]
        have hmap : D''.map f = (p : ℚ) • D.map f - C.map f * adjugate (P.map f) * B.map f := by
          simp only [D'']
          rw [Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul, hadj]
          congr 1
          ext x y
          show f (p * D x y) = (p : ℚ) * f (D x y)
          rw [map_mul]; rfl
        rw [hmap]
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hp0, one_smul, Matrix.mul_smul,
          Matrix.smul_mul]
      have h1 := det_fromBlocks₁₁ (P.map f) (B.map f) (C.map f) (D.map f)
      rw [← fromBlocks_map, ← hblk, hsub, hG, hschur, det_smul, hκ, hPdet, hD''] at h1
      have : ((p ^ m * G.det : ℤ) : ℚ) = ((p * D''.det : ℤ) : ℚ) := by
        rw [Int.cast_mul, Int.cast_pow, Int.cast_mul]
        rw [h1]
        have hpm : (p : ℚ) ^ m * ((p : ℚ)⁻¹) ^ m = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hp0, one_pow]
        linear_combination ((p : ℚ) * (D''.det : ℚ)) * hpm
      exact_mod_cast this
    have hDodd : Odd D''.det := by
      have : Odd (p * D''.det) := key ▸ (hpodd.pow.mul hO)
      exact (Int.odd_mul.mp this).2
    obtain ⟨h', hm, hdet'⟩ := ih m (by omega) D'' hκ hDsym hDeven hDodd
    refine ⟨h' + 1, by omega, ?_⟩
    have hp2 : p ^ 2 ≡ 1 [ZMOD 4] := by simpa using hp4.pow 2
    have hpm : p ^ m ≡ 1 [ZMOD 4] := by
      rw [hm, pow_mul]; simpa using hp2.pow h'
    calc G.det = 1 * G.det := by ring
      _ ≡ p ^ m * G.det [ZMOD 4] := hpm.symm.mul_right _
      _ = p * D''.det := key
      _ ≡ (-1) * (-1) ^ h' [ZMOD 4] := hp4.mul hdet'
      _ = (-1) ^ (h' + 1) := by ring

/-- **(F5)** An even integral symmetric matrix of odd determinant has even size `2h`, and its
determinant is `≡ (-1)^h (mod 4)`. -/
theorem even_det_odd {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℤ)
    (hS : G.IsSymm) (hE : ∀ i, Even (G i i)) (hO : Odd G.det) :
    ∃ h : ℕ, Fintype.card ι = 2 * h ∧ G.det ≡ (-1) ^ h [ZMOD 4] :=
  even_det_odd_aux _ G rfl hS hE hO

end F5

end Parity
