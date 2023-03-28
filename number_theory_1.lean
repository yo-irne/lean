import tactic

example (P : Prop) : P → P :=
begin
intros grzes,
exact grzes,
end

example (P Q : Prop) : P ∧ Q → P :=
begin
rintros ⟨lewy_grzes, _⟩,
-- cases grzes with lewy_grzes prawy_grzes,
exact lewy_grzes,
end

def P (n : ℕ) : Prop := ∀m>0,m∣n → (m = 1 ∨ m = n)

theorem yo (n : ℕ) (hn : 0 < n) : (n + 1) ∣ (n^2 + 1) ↔ n = 1 :=
begin
  split,
  { rintro ⟨c, hc⟩,
    have h1 : (n : ℤ)^2 - 1 = (n + 1) * (n - 1) := by ring,
    zify at hc,
    have h2 : (n : ℤ) + 1 ∣ 2,
    { use c - (n - 1),
      rw [ mul_sub, ← hc, ← h1 ],
      ring },
    have h3 : (n : ℤ) + 1 ≤ 2 := int.le_of_dvd zero_lt_two h2,
    have h4 : n + 1 ≤ 2,
    exact_mod_cast h3,
    linarith },
  { rintro rfl,
    norm_num },
end
