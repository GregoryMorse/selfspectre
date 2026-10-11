module
public import WriteExecute.Model.Run

public section

namespace WriteExecute.WE

/-- C05 (word model): a jump whose displacement field holds `e - (c + 2)` lands on the entry at `e`;
an entry `[MOV res f; JMP ret]` then stores `f` into the result field `res` and returns to `ret`. -/
theorem lookup_correct (m : Int → Int) (c e res ret f : Int)
    (hj : m c = 2) (hd : m (c + 1) = e - (c + 2))
    (h1 : m e = 1) (h2 : m (e + 1) = res - (e + 3)) (h3 : m (e + 2) = f)
    (h4 : m (e + 3) = 2) (h5 : m (e + 4) = ret - (e + 5))
    (hr3 : res ≠ e + 3) (hr4 : res ≠ e + 4) :
    run 3 ⟨c, m⟩ = (.running, ⟨ret, write m res f⟩) := by
  have s1 : step ⟨c, m⟩ = (.running, ⟨e, m⟩) := by
    have : c + 2 + m (c + 1) = e := by rw [hd]; omega
    simp [step, decode, hj, this]
  have s2 : step ⟨e, m⟩ = (.running, ⟨e + 3, write m res f⟩) := by
    have : e + 3 + m (e + 1) = res := by rw [h2]; omega
    simp [step, decode, h1, this, h3]
  have s3 : step ⟨e + 3, write m res f⟩ = (.running, ⟨ret, write m res f⟩) := by
    have e1 : write m res f (e + 3) = 2 := by simp [write, Ne.symm hr3, h4]
    have e2 : write m res f (e + 3 + 1) = ret - (e + 5) := by
      have : e + 3 + 1 = e + 4 := by omega
      rw [this]; simp [write, Ne.symm hr4, h5]
    have : e + 3 + 2 + (ret - (e + 5)) = ret := by omega
    simp [step, decode, e1, e2, this]
  simp [run, s1, s2, s3]

/-- The table form: entry `k` lives at `base + stride * k`; every entry stores its own value `f k`. -/
theorem lookup_table (m : Int → Int) (base stride : Int) (n : Nat) (f : Nat → Int)
    (c res ret : Int) (k : Nat) (hk : k < n)
    (hj : m c = 2) (hd : m (c + 1) = base + stride * (k : Int) - (c + 2))
    (hT : ∀ i : Nat, i < n →
      m (base + stride * (i : Int)) = 1 ∧
      m (base + stride * (i : Int) + 1) = res - (base + stride * (i : Int) + 3) ∧
      m (base + stride * (i : Int) + 2) = f i ∧
      m (base + stride * (i : Int) + 3) = 2 ∧
      m (base + stride * (i : Int) + 4) = ret - (base + stride * (i : Int) + 5))
    (hr3 : res ≠ base + stride * (k : Int) + 3) (hr4 : res ≠ base + stride * (k : Int) + 4) :
    run 3 ⟨c, m⟩ = (.running, ⟨ret, write m res (f k)⟩) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT k hk
  exact lookup_correct m c _ res ret (f k) hj hd h1 h2 h3 h4 h5 hr3 hr4

end WriteExecute.WE
