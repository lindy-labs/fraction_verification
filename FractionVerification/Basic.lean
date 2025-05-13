import FractionVerification.Load

namespace Sierra

def Bytes31.toFelt (x : Bytes31) : F := x.toNat -- TODO why can't we use `x.toFin.castLE (m := PRIME) (by simp [PRIME])`

end Sierra

open Sierra

aegis_spec "core::panic_with_const_felt252<155785504323917466144735657540098748279>" :=
  fun _ ρ =>
  ρ = ⟨(), [155785504323917466144735657540098748279]⟩

aegis_prove "core::panic_with_const_felt252<155785504323917466144735657540098748279>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<9163530612918341685758827355588318787825527>" :=
  fun _ ρ =>
  ρ = ⟨(), [9163530612918341685758827355588318787825527]⟩

aegis_prove "core::panic_with_const_felt252<9163530612918341685758827355588318787825527>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<35795041456712272209994989265157601652599>" :=
  fun _ ρ =>
  ρ = ⟨(), [35795041456712272209994989265157601652599]⟩

aegis_prove "core::panic_with_const_felt252<35795041456712272209994989265157601652599>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<29721761890975875353235833581453094220424382983267374>" :=
  fun _ ρ =>
  ρ = ⟨(), [29721761890975875353235833581453094220424382983267374]⟩

aegis_prove "core::panic_with_const_felt252<29721761890975875353235833581453094220424382983267374>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<155785504329508738615720351733824384887>" :=
  fun _ ρ =>
  ρ = ⟨(), [155785504329508738615720351733824384887]⟩

aegis_prove "core::panic_with_const_felt252<155785504329508738615720351733824384887>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::panic_with_const_felt252<573087285299505011920718992710461799>" :=
  fun _ ρ =>
  ρ = ⟨(), [573087285299505011920718992710461799]⟩

aegis_prove "core::panic_with_const_felt252<573087285299505011920718992710461799>" :=
  fun _ ρ => by
  rintro rfl
  rfl

aegis_spec "core::array::serialize_array_helper<core::bytes_31::bytes31, core::serde::into_felt252_based::SerdeImpl<core::bytes_31::bytes31, core::bytes_31::bytes31Copy, core::bytes_31::Bytes31IntoFelt252, core::bytes_31::Felt252TryIntoBytes31>, core::bytes_31::bytes31Drop>" :=
  fun _ _ _ data str _ _ ρ =>
  ρ = .inl (str ++ data.map Sierra.Bytes31.toFelt, ()) ∨
    ρ.isRight

aegis_prove "core::array::serialize_array_helper<core::bytes_31::bytes31, core::serde::into_felt252_based::SerdeImpl<core::bytes_31::bytes31, core::bytes_31::bytes31Copy, core::bytes_31::Bytes31IntoFelt252, core::bytes_31::Felt252TryIntoBytes31>, core::bytes_31::bytes31Drop>" :=
  fun _ _ _ data str _ _ ρ => by
  unfold_spec "core::array::serialize_array_helper<core::bytes_31::bytes31, core::serde::into_felt252_based::SerdeImpl<core::bytes_31::bytes31, core::bytes_31::bytes31Copy, core::bytes_31::Bytes31IntoFelt252, core::bytes_31::Felt252TryIntoBytes31>, core::bytes_31::bytes31Drop>"
  aesop (add simp [Sierra.Bytes31.toFelt])

aegis_info "core::bytes_31::one_shift_left_bytes_felt252"

aegis_spec "core::bytes_31::one_shift_left_bytes_felt252" :=
  fun _ _ a _ ρ =>
  a ≤ 16 ∧ ρ = .inl (10 ^ a.toNat) ∨
    a > 16 ∧ ρ.isRight

set_option maxHeartbeats 1_000_000 in
aegis_prove "core::bytes_31::one_shift_left_bytes_felt252" :=
  fun _ _ a _ ρ => by
  unfold_spec "core::bytes_31::one_shift_left_bytes_felt252"
  --aesop
  sorry

abbrev Fraction := Int128 × UInt128

def Fraction.toRat (r : Fraction) : ℚ := r.1.toInt / r.2.toNat

aegis_spec "fraction_verification::fraction::FractionPartialOrd::lt" :=
  fun _ _ (a b : Fraction) _ ρ =>
  ρ = .inl (Bool.toSierraBool (a.toRat < b.toRat)) ∨
    ρ.isRight

set_option maxHeartbeats 1_000_000 in
aegis_prove "fraction_verification::fraction::FractionPartialOrd::lt" :=
  fun _ _ (a b : Fraction) _ ρ => by
  unfold_spec "fraction_verification::fraction::FractionPartialOrd::lt"
  aesop
  sorry

aegis_complete
