import FractionVerification.Load
import CorelibVerification

open Sierra

abbrev Fraction := Int128 × UInt128

def Fraction.toRat (r : Fraction) : ℚ := r.1.toInt / r.2.toNat

def Fraction.num (r : Fraction) := r.1

def Fraction.denom (r : Fraction) := r.2

aegis_spec "fraction_verification::abs::abs<core::integer::i128, core::integer::I128PartialOrd, core::integer::I128Neg, core::integer::i128Drop, core::integer::i128Copy, core::integer::I128Zero, core::integer::u128, core::integer::DowncastableIntTryInto<core::integer::i128, core::integer::u128, core::integer::DowncastableI128, core::integer::DowncastableU128, _>>" :=
  fun _ _ a _ ρ =>
  a ≠ BitVec.intMin 128 ∧ ρ = .inl a.abs ∨
    a = BitVec.intMin 128 ∧ ρ.isRight

aegis_prove "fraction_verification::abs::abs<core::integer::i128, core::integer::I128PartialOrd, core::integer::I128Neg, core::integer::i128Drop, core::integer::i128Copy, core::integer::I128Zero, core::integer::u128, core::integer::DowncastableIntTryInto<core::integer::i128, core::integer::u128, core::integer::DowncastableI128, core::integer::DowncastableU128, _>>" :=
  fun _ _ a _ ρ => by
  unfold_spec "fraction_verification::abs::abs<core::integer::i128, core::integer::I128PartialOrd, core::integer::I128Neg, core::integer::i128Drop, core::integer::i128Copy, core::integer::I128Zero, core::integer::u128, core::integer::DowncastableIntTryInto<core::integer::i128, core::integer::u128, core::integer::DowncastableI128, core::integer::DowncastableU128, _>>"
  rintro ⟨_,_,_,_,_,_,_,_,(⟨h₁,h₂,h₃⟩|⟨h₁,h₂,h₃⟩)⟩
  · rcases h₃ with (⟨rfl,h₃,h₄⟩|h₃)
    · rcases h₄ with (⟨rfl,rfl⟩|h₄)
      · simp [BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le, BitVec.slt_eq_decide] at *
        rcases h₂ with ⟨h₂,rfl⟩
        rcases h₃ with ⟨h₃,rfl⟩
        simp [BitVec.toInt_neg_of_ne_intMin h₂] at *
        rw [← BitVec.neg_eq]
        bv_decide
      · rcases h₃ with (h₃|h₃)
        · simp [BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le, BitVec.slt_eq_decide] at *
          rcases h₂ with ⟨-,rfl⟩
          rcases h₃ with ⟨-,rfl⟩
          simp at h₄
        · simp [BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le, BitVec.slt_eq_decide] at *
          rcases h₂ with ⟨h₂,rfl⟩
          rcases h₃ with ⟨h₃,rfl⟩
          rw [BitVec.toInt_neg_of_ne_intMin h₂] at h₃
          omega
    · rcases h₂ with (h₂|h₂)
      · rcases h₂ with ⟨-,rfl⟩
        simp at h₃
      · rcases h₃ with ⟨rfl,rfl⟩
        rcases h₂ with ⟨rfl,-⟩
        simp
  · rcases h₃ with (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · simp [BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le] at h₁ h₂ ⊢
      exact ⟨fun h => by subst h; bv_decide, h₂.2⟩
    · simp [BitVec.slt_iff_toInt_lt] at h₁ h₂ ⊢
      omega

aegis_spec "fraction_verification::abs::AbsImplI128::abs" :=
  fun _ _ a _ ρ =>
  a ≠ BitVec.intMin 128 ∧ ρ = .inl a.abs ∨
    a = BitVec.intMin 128 ∧ ρ.isRight

aegis_prove "fraction_verification::abs::AbsImplI128::abs" :=
  fun _ _ a _ ρ => by
  unfold_spec "fraction_verification::abs::AbsImplI128::abs"
  aesop

theorem lt_aux1 {x y : BitVec w} (hx : ¬ x.slt 0) (hy : ¬ y.slt 0) : x < y ↔ x.slt y :=
  ⟨fun h => by bv_decide, fun h => by bv_decide⟩

theorem lt_aux2 {x : BitVec 128} : x.toNat = (0#128 ++ x).toInt := by
  rw [BitVec.toInt_eq_toNat_of_msb (by bv_decide)]
  congr 1
  rw [← BitVec.toNat_setWidth' (n := 256) (by simp), BitVec.toNat_inj,
    BitVec.setWidth'_eq]
  bv_decide

theorem lt_aux3 {x : BitVec 128} (hx : (0#128).sle x = «true») : x.toInt = (0#128 ++ x).toInt := by
  rw [← BitVec.toInt_signExtend_of_le (x := x) (v := 256) (by simp), BitVec.toInt_inj]
  bv_decide

theorem lt_aux3' {x : BitVec 128} (hx : x.sle 0#128) :
    x.toInt = - (0#128 ++ x.abs).toInt := by
  rw [← BitVec.toInt_neg_of_ne_intMin (by bv_decide),
    ← BitVec.toInt_signExtend_of_le (v := 256) (by simp)]
  congr 1
  bv_decide

set_option grind.warning false in
theorem lt_aux4 {x y : BitVec 256} (h : ¬ x.smulOverflow y) : x.toInt * y.toInt = (x * y).toInt := by
  rw [@BitVec.toInt_mul]
  unfold BitVec.smulOverflow at h
  symm
  apply Int.bmod_eq_of_le_mul_two
  <;> grind

theorem lt_aux5 {x : BitVec 128} (h : BitVec.sle 0 x) : x.abs = x := by
  bv_decide

theorem lt_aux5' {x : BitVec 128} (h : BitVec.sle x 0) : x.abs = - x := by
  bv_decide

aegis_spec "fraction_verification::fraction::FractionPartialOrd::lt" :=
  fun _ _ (a b : Fraction) _ ρ =>
  0 < a.denom → 0 < b.denom →
  ρ = .inl (Bool.toSierraBool (a.toRat < b.toRat)) ∨
    ρ.isRight

set_option maxHeartbeats 1_000_000 in
--set_option pp.notation false in
-- set_option profiler true in
aegis_prove "fraction_verification::fraction::FractionPartialOrd::lt" :=
  fun _ _ (a b : Fraction) _ ρ => by
  unfold_spec "fraction_verification::fraction::FractionPartialOrd::lt"
  rintro ⟨_,_,_,_,_,_,_,_,_,_,h⟩
  intro ha hb
  rcases h with ⟨_,_,_,_,_,_,_,_,_,_,h⟩
  rcases h with ⟨_,_,_,_,_,_,_,_,_,_,h⟩
  rcases h with ⟨_,_,_,_,_,_,rfl,(⟨h₁,h₂⟩|⟨h₁,rfl,h₂⟩)⟩
  · rcases h₂ with (⟨h₂,h₃⟩|⟨h₂,rfl,h₃⟩)
    · rcases h₃ with (⟨h₃,rfl,h₅,h₆⟩|⟨h₃,rfl,h₄⟩)
      · rcases h₆ with (⟨rfl,h₇,h₈⟩|⟨rfl,rfl⟩)
        · rcases h₈ with (⟨rfl,h₉,h₁₀⟩|⟨rfl,rfl⟩)
          · rcases h₁₀ with (⟨rfl,h₁₁,h₁₂⟩|⟨rfl,rfl⟩)
            · rcases h₁₂ with (⟨rfl,h₁₃⟩|⟨rfl,rfl⟩)
              · rcases h₁₃ with (⟨h₁₃,rfl⟩|⟨h₁₃,rfl⟩)
                · simp only [Bool.toSierraBool_iff_eq_false', ne_eq, Nat.ofNat_pos, Sum.inl.injEq,
                  Sum.isRight_inl, Bool.false_eq_true, and_false, or_false, Nat.reduceAdd,
                  BitVec.ofNat_eq_ofNat, Bool.not_eq_true, gt_iff_lt] at *
                  rcases h₇ with ⟨h₇,rfl⟩
                  rcases h₁₁ with ⟨h₁₁,rfl⟩
                  congr 2
                  simp only [UInt256.mul_def, Nat.reduceAdd, UInt256.append_ofBitVec,
                    Fraction.toRat, eq_iff_iff]
                  bv_decide
                · simp only [Bool.toSierraBool_iff_eq_false', ne_eq, Nat.ofNat_pos, Sum.inl.injEq,
                  Sum.isRight_inl, Bool.false_eq_true, and_false, or_false, Nat.reduceAdd,
                  BitVec.ofNat_eq_ofNat, Bool.not_eq_true, Bool.toSierraBool_iff_eq_true'] at *
                  rcases h₅ with ⟨h₅,rfl⟩
                  rcases h₇ with ⟨h₇,rfl⟩
                  rcases h₉ with ⟨h₉,rfl⟩
                  rcases h₁₁ with ⟨h₁₁,rfl⟩
                  congr 2
                  simp only [UInt256.mul_def, Nat.reduceAdd, UInt256.append_ofBitVec,
                    Fraction.toRat, eq_iff_iff]
                  bv_decide
              · simp
            · simp
          · simp
        · simp
      · rcases h₄ with (⟨h₄,h₅,h₆⟩|⟨h₄,rfl⟩)
        · rcases h₆ with (⟨rfl,h₆,h₇⟩|⟨rfl,rfl⟩)
          · rcases h₇ with (⟨rfl,h₇,h₈⟩|⟨rfl,rfl⟩)
            · rcases h₈ with (⟨rfl,h₈,h₉⟩|⟨rfl,rfl⟩)
              · rcases h₉ with (⟨rfl,h₉⟩|⟨rfl,rfl⟩)
                · rcases h₉ with (⟨h₉,rfl⟩|⟨h₉,rfl⟩)
                  · simp only [Bool.toSierraBool_iff_eq_false', Bool.toSierraBool_iff_eq_true',
                    decide_eq_false_iff_not, ne_eq, Nat.ofNat_pos, Sum.inl.injEq, Sum.isRight_inl,
                    Bool.false_eq_true, and_false, or_false, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
                    Bool.not_eq_true, gt_iff_lt] at *
                    rcases h₆ with ⟨h₆,rfl⟩
                    rcases h₇ with ⟨h₇,rfl⟩
                    rcases h₈ with ⟨h₈,rfl⟩
                    congr 2
                    simp only [UInt256.mul_def, Nat.reduceAdd, UInt256.append_ofBitVec,
                      Fraction.toRat, eq_iff_iff]
                    bv_decide
                  · simp only [Bool.toSierraBool_iff_eq_false', Bool.toSierraBool_iff_eq_true',
                    decide_eq_false_iff_not, ne_eq, Nat.ofNat_pos, Sum.inl.injEq, Sum.isRight_inl,
                    Bool.false_eq_true, and_false, or_false, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
                    Bool.not_eq_true] at *
                    rcases h₅ with ⟨h₅,rfl⟩
                    rcases h₆ with ⟨h₆,rfl⟩
                    rcases h₇ with ⟨h₇,rfl⟩
                    rcases h₈ with ⟨h₈,rfl⟩
                    congr 2
                    simp only [UInt256.mul_def, Nat.reduceAdd, UInt256.append_ofBitVec,
                      Fraction.toRat, eq_iff_iff]
                    bv_decide
                · simp
              · simp
            · simp
          · simp
        · simp at *
          bv_decide
    · rcases h₃ with (⟨h₃,h₄⟩|⟨h₃,rfl⟩)
      · rcases h₄ with (⟨h₄,h₅,h₆,h₇⟩|⟨h₄,h₅,h₆⟩)
        · cases h₅
          rcases h₇ with (⟨rfl,h₇,h₈⟩|⟨-,rfl⟩)
          · rcases h₈ with (⟨rfl,h₈,h₉⟩|⟨-,rfl⟩)
            · rcases h₉ with (⟨rfl,h₉,h₁₀⟩|⟨_,rfl⟩)
              · rcases h₁₀ with (⟨rfl,h₁₀⟩|⟨_,rfl⟩)
                · rcases h₁₀ with (⟨h₁₀,rfl⟩|⟨h₁₀,rfl⟩)
                  · simp [Fraction.toRat] at *
                    bv_decide
                  · simp [Fraction.toRat, Fraction.denom] at *
                    rcases h₆ with ⟨h₆,rfl⟩
                    rcases h₇ with ⟨h₇,rfl⟩
                    rcases h₈ with ⟨h₈,rfl⟩
                    rcases h₉ with ⟨h₉,rfl⟩
                    simp only [UInt256.mul_def, Nat.reduceAdd, UInt256.append_ofBitVec]
                    congr 2
                    rw [lt_aux1 (by bv_decide) (by bv_decide), BitVec.slt_iff_toInt_lt]
                    rw [div_lt_div_iff₀ (by simp [BitVec.lt_def] at ha; erw [Nat.cast_lt]; assumption)
                        (by simp [BitVec.lt_def] at hb; erw [Nat.cast_lt]; assumption)]
                    norm_cast
                    congr
                    · rw [lt_aux2, lt_aux3 h₂, lt_aux4 (by bv_decide), lt_aux5 h₂]
                    · rw [lt_aux2, lt_aux3 (by bv_decide), lt_aux4 (by bv_decide), lt_aux5 (by bv_decide)]
                · right; simp
              · right; simp
            · right; simp
          · right; simp
        · rcases h₆ with (⟨h₆,h₇,h₈⟩|⟨_,rfl⟩)
          · cases h₅
            rcases h₈ with (⟨rfl,h₈,h₉⟩|⟨_,rfl⟩)
            · rcases h₉ with (⟨rfl,h₉,h₁₀⟩|⟨_,rfl⟩)
              · rcases h₁₀ with (⟨rfl,h₁₀,h₁₁⟩|⟨_,rfl⟩)
                · rcases h₁₁ with (⟨rfl,h₁₁⟩|⟨_,rfl⟩)
                  · rcases h₁₁ with (⟨h₁₁,rfl⟩|⟨h₁₁,rfl⟩)
                    · simp only [BitVec.ofNat_eq_ofNat, Bool.toSierraBool_iff_eq_false',
                      Bool.toSierraBool_iff_eq_true', decide_eq_false_iff_not, ne_eq, Nat.ofNat_pos,
                      Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false,
                      Nat.reduceAdd, Bool.not_eq_true, gt_iff_lt, Fraction.toRat] at *
                      bv_decide
                    · simp only [BitVec.ofNat_eq_ofNat, Bool.toSierraBool_iff_eq_false',
                      Bool.toSierraBool_iff_eq_true', decide_eq_false_iff_not, ne_eq, Nat.ofNat_pos,
                      Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false, or_false,
                      Nat.reduceAdd, Bool.not_eq_true, Fraction.toRat] at *
                      bv_decide
                  · right; simp
                · right; simp
              · right; simp
            · right; simp
          · cases h₅
            simp_all
      · simp [Fraction.toRat, Fraction.denom] at *
        trans 0
        · apply div_nonpos_of_nonpos_of_nonneg
          · norm_cast
            erw [← BitVec.sle_iff_toInt_le (y := 0#128)]
            assumption
          · simp
        · apply Rat.div_nonneg
          · norm_cast
            erw [← BitVec.sle_iff_toInt_le (x := 0#128)]
            assumption
          · simp
  · rcases h₂ with (⟨h₂,h₃⟩|⟨h₂,rfl⟩)
    · rcases h₃ with (⟨h₃,h₄⟩|h₃)
      · rcases h₄ with (⟨h₄,h₅,h₆,h₇⟩|⟨h₄,h₅,h₆⟩)
        · cases h₅
          rcases h₇ with (⟨rfl,h₇,h₈⟩|⟨_,rfl⟩)
          · rcases h₈ with (⟨rfl,h₈,h₉⟩|⟨_,rfl⟩)
            · rcases h₉ with (⟨rfl,h₁₀,h₁₁⟩|⟨_,rfl⟩)
              · rcases h₁₁ with (⟨rfl,h₁₁⟩|⟨_,rfl⟩)
                · rcases h₁₁ with (⟨h₁₁,rfl⟩|⟨h₁₁,rfl⟩)
                  · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom,
                    Bool.toSierraBool_iff_eq_true', Bool.toSierraBool_iff_eq_false', ne_eq,
                    Nat.ofNat_pos, Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false,
                    or_false, Nat.reduceAdd, Bool.not_eq_true, gt_iff_lt, Fraction.toRat] at *
                    bv_decide
                  · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom,
                    Bool.toSierraBool_iff_eq_true', Bool.toSierraBool_iff_eq_false', ne_eq,
                    Nat.ofNat_pos, Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false,
                    or_false, Nat.reduceAdd, Bool.not_eq_true, Fraction.toRat] at *
                    bv_decide
                · right; simp
              · right; simp
            · right; simp
          · right; simp
        · cases h₅
          rcases h₆ with (⟨h₆,h₇,h₈⟩|⟨h₆,rfl⟩)
          · rcases h₈ with (⟨rfl,h₉,h₁₀⟩|⟨_,rfl⟩)
            · rcases h₁₀ with (⟨rfl,h₁₀,h₁₁⟩|⟨_,rfl⟩)
              · rcases h₁₁ with (⟨rfl,h₁₁,h₁₂⟩|⟨_,rfl⟩)
                · rcases h₁₂ with (⟨rfl,h₁₂⟩|⟨_,rfl⟩)
                  · rcases h₁₂ with (⟨h₁₂,rfl⟩|⟨h₁₂,rfl⟩)
                    · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom,
                      Bool.toSierraBool_iff_eq_true', Bool.toSierraBool_iff_eq_false',
                      decide_eq_false_iff_not, ne_eq, Nat.ofNat_pos, Sum.inl.injEq, Sum.isRight_inl,
                      Bool.false_eq_true, and_false, or_false, Nat.reduceAdd, Bool.not_eq_true,
                      gt_iff_lt, Fraction.toRat] at *
                      congr 2
                      rcases h₇ with ⟨h₇,rfl⟩
                      rcases h₉ with ⟨h₉,rfl⟩
                      rcases h₁₀ with ⟨h₁₀,rfl⟩
                      rcases h₁₁ with ⟨h₁₁,rfl⟩
                      simp [UInt256.mul_def, UInt256.append_ofBitVec]
                      rw [lt_aux1 (by bv_decide) (by bv_decide), BitVec.slt_iff_toInt_lt]
                      rw [div_lt_div_iff₀ (by simp [BitVec.lt_def] at ha; erw [Nat.cast_lt]; assumption)
                          (by simp [BitVec.lt_def] at hb; erw [Nat.cast_lt]; assumption)]
                      norm_cast
                      rw [lt_aux2, lt_aux2, lt_aux3' h₁, Int.neg_mul, neg_lt, ← Int.neg_mul,
                        ← BitVec.toInt_neg_of_ne_intMin h₁₀, lt_aux3 (by bv_decide)]
                      rw [lt_aux4 (by bv_decide), lt_aux4 (by bv_decide)]
                      rw [lt_aux5' (by bv_decide)]
                    · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom,
                      Bool.toSierraBool_iff_eq_true', Bool.toSierraBool_iff_eq_false',
                      decide_eq_false_iff_not, ne_eq, Nat.ofNat_pos, Sum.inl.injEq, Sum.isRight_inl,
                      Bool.false_eq_true, and_false, or_false, Nat.reduceAdd, Bool.not_eq_true,
                      Fraction.toRat] at *
                      bv_decide
                  · right; simp
                · right; simp
              · right; simp
            · right; simp
          · simp_all only [BitVec.ofNat_eq_ofNat, Fraction.denom, Bool.toSierraBool_iff_eq_false',
            Bool.toSierraBool_iff_eq_true', Fraction.toRat, Sum.inl.injEq, decide_eq_true_eq,
            Sum.isRight_inl, Bool.false_eq_true, or_false, Bool.toSierraBool_true,
            Bool.toSierraBool_iff_eq_true, Bool.toSierraBool_false, Bool.toSierraBool_iff_eq_false,
            BitVec.toInt_zero, Int.cast_zero, zero_div]
            apply div_neg_of_neg_of_pos
            · norm_cast
              erw [← BitVec.slt_iff_toInt_lt (y := 0#128)]
              assumption
            · norm_cast
      · rcases h₃ with ⟨h₃,h₄,h₅⟩
        cases h₄
        rcases h₅ with (⟨h₅,h₆⟩|⟨h₅,rfl⟩)
        · rcases h₆ with (⟨h₆,h₇,h₈,h₉⟩|⟨h₆,h₇,h₈⟩)
            <;> cases h₇
          · rcases h₉ with (⟨rfl,h₉,h₁₀⟩|⟨_,rfl⟩)
            · rcases h₁₀ with (⟨rfl,h₁₀,h₁₁⟩|⟨_,rfl⟩)
              · rcases h₁₁ with (⟨rfl,h₁₁,h₁₂⟩|⟨_,rfl⟩)
                · rcases h₁₂ with (⟨rfl,h₁₂⟩|⟨_,rfl⟩)
                  · rcases h₁₂ with (⟨h₁₂,rfl⟩|⟨h₁₂,rfl⟩)
                    · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom,
                      Bool.toSierraBool_iff_eq_true', Bool.toSierraBool_iff_eq_false', ne_eq,
                      Nat.ofNat_pos, Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false,
                      or_false, Nat.reduceAdd, Bool.not_eq_true, gt_iff_lt, Fraction.toRat] at *
                      bv_decide
                    · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom,
                      Bool.toSierraBool_iff_eq_true', Bool.toSierraBool_iff_eq_false', ne_eq,
                      Nat.ofNat_pos, Sum.inl.injEq, Sum.isRight_inl, Bool.false_eq_true, and_false,
                      or_false, Nat.reduceAdd, Bool.not_eq_true, Fraction.toRat] at *
                      bv_decide
                  · right; simp
                · right; simp
              · right; simp
            · right; simp
          · rcases h₈ with (⟨h₈,h₉,h₁₀⟩|⟨h₈,rfl⟩)
            · rcases h₁₀ with (⟨rfl,h₁₀,h₁₁⟩|⟨_,rfl⟩)
              · rcases h₁₁ with (⟨rfl,h₁₁,h₁₂⟩|⟨_,rfl⟩)
                · rcases h₁₂ with (⟨rfl,h₁₂,h₁₃⟩|⟨_,rfl⟩)
                  · rcases h₁₃ with (⟨rfl,h₁₃⟩|⟨_,rfl⟩)
                    · rcases h₁₃ with (⟨h₁₃,rfl⟩|⟨h₁₃,rfl⟩)
                      · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom,
                        Bool.toSierraBool_iff_eq_true', Bool.toSierraBool_iff_eq_false',
                        decide_eq_false_iff_not, ne_eq, Nat.ofNat_pos, Sum.inl.injEq,
                        Sum.isRight_inl, Bool.false_eq_true, and_false, or_false, Nat.reduceAdd,
                        Bool.not_eq_true, gt_iff_lt, Fraction.toRat] at *
                        bv_decide
                      · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom,
                        Bool.toSierraBool_iff_eq_true', Bool.toSierraBool_iff_eq_false',
                        decide_eq_false_iff_not, ne_eq, Nat.ofNat_pos, Sum.inl.injEq,
                        Sum.isRight_inl, Bool.false_eq_true, and_false, or_false, Nat.reduceAdd,
                        Bool.not_eq_true, Fraction.toRat] at *
                        bv_decide
                    · right; simp
                  · right; simp
                · right; simp
              · right; simp
            · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom, Bool.toSierraBool_iff_eq_true',
              Bool.toSierraBool_iff_eq_false', decide_eq_true_eq, Fraction.toRat, Sum.inl.injEq,
              Sum.isRight_inl, Bool.false_eq_true, or_false] at *
              bv_decide
        · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom, Bool.toSierraBool_iff_eq_true',
          Bool.toSierraBool_iff_eq_false', Fraction.toRat, Sum.inl.injEq, decide_eq_false_iff_not,
          not_lt, Sum.isRight_inl, Bool.false_eq_true, or_false] at *
          trans 0
          · apply div_nonpos_of_nonpos_of_nonneg <;> norm_cast
            · erw [← BitVec.sle_iff_toInt_le (y := 0#128)]
              assumption
            · erw [← BitVec.le_def (x := 0#128)]
              bv_decide
          · apply le_of_eq
            symm
            rw [div_eq_zero_iff]
            left
            norm_cast
            erw [BitVec.toInt_inj (y := 0#128)]
            bv_decide
    · simp only [BitVec.ofNat_eq_ofNat, Fraction.denom, Bool.toSierraBool_iff_eq_true',
      Fraction.toRat, Sum.inl.injEq, decide_eq_true_eq, Sum.isRight_inl, Bool.false_eq_true,
      or_false] at *
      apply lt_of_le_of_lt
      · apply div_nonpos_of_nonpos_of_nonneg
        · norm_cast
          erw [← BitVec.sle_iff_toInt_le (y := 0#128)]
          assumption
        · simp
      · apply div_pos
        · norm_cast
          erw [← BitVec.slt_iff_toInt_lt (x := 0#128)]
          assumption
        · norm_cast

aegis_spec "fraction_verification::fraction::FractionlImpl::new" :=
  fun _ n d ρ =>
  d ≠ 0 ∧ ρ = .inl (n, d) ∨
    d = 0 ∧ ρ.isRight

aegis_prove "fraction_verification::fraction::FractionlImpl::new" :=
  fun _ n d ρ => by
  unfold_spec "fraction_verification::fraction::FractionlImpl::new"
  aesop

aegis_spec "fraction_verification::fraction::FractionPartialOrd::gt" :=
  fun _ _ (a b : Fraction) _ ρ =>
  0 < a.denom → 0 < b.denom →
  ρ = .inl (Bool.toSierraBool (b.toRat < a.toRat)) ∨
    ρ.isRight

aegis_prove "fraction_verification::fraction::FractionPartialOrd::gt" :=
  fun _ _ (a b : Fraction) _ ρ => by
  unfold_spec "fraction_verification::fraction::FractionPartialOrd::gt"
  aesop

aegis_spec "fraction_verification::fraction::fv::fraction_parial_ord_test" :=
  fun _ _ _ _ =>
  True

set_option maxHeartbeats 1_000_000 in
aegis_prove "fraction_verification::fraction::fv::fraction_parial_ord_test" :=
  fun _ _ _ ρ => by
  intro
  trivial

aegis_complete
