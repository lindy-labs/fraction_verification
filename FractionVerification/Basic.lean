import FractionVerification.Load
import CorelibVerification

open Sierra

abbrev Fraction := Int128 × UInt128

def Fraction.toRat (r : Fraction) : ℚ := r.1.toInt / r.2.toNat

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
          rcases h₂ with ⟨h₂,rfl⟩
          rcases h₃ with ⟨h₃,rfl⟩
          simp at h₄
        · simp [BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le, BitVec.slt_eq_decide] at *
          rcases h₂ with ⟨h₂,rfl⟩
          rcases h₃ with ⟨h₃,rfl⟩
          rw [BitVec.toInt_neg_of_ne_intMin h₂] at h₃
          omega
    · rcases h₂ with (h₂|h₂)
      · rcases h₂ with ⟨h₂,rfl⟩
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

aegis_spec "fraction_verification::fraction::FractionPartialOrd::lt" :=
  fun _ _ (a b : Fraction) _ ρ =>
  ρ = .inl (Bool.toSierraBool (a.toRat < b.toRat)) ∨
    ρ.isRight

set_option maxHeartbeats 1_000_000 in
aegis_prove "fraction_verification::fraction::FractionPartialOrd::lt" :=
  fun _ _ (a b : Fraction) _ ρ => by
  unfold_spec "fraction_verification::fraction::FractionPartialOrd::lt"
  sorry

aegis_complete
