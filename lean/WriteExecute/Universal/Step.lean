module
public import WriteExecute.Universal.Layout
public import WriteExecute.Model.Run

public section

namespace WriteExecute.Universal

open WriteExecute.TM

/-- Memory after the first `i` entry rewrites of the cell that starts at address `b`. -/
@[expose] def patch (A Q : Nat) (b : Int) (sym : Nat) : Nat → (Int → Int) → (Int → Int)
  | 0, m => m
  | i + 1, m => write (patch A Q b sym i m) (b + 2 * (i : Int) + 1) (entryDisp A Q i sym)

theorem patch_hit (A Q : Nat) (b : Int) (sym : Nat) (m : Int → Int) :
    ∀ (i j : Nat), j < i → patch A Q b sym i m (b + 2 * (j : Int) + 1) = entryDisp A Q j sym := by
  intro i
  induction i with
  | zero => intro j hj; omega
  | succ i ih =>
    intro j hj
    by_cases e : j = i
    · subst e; simp [patch, write]
    · have hne : b + 2 * (j : Int) + 1 ≠ b + 2 * (i : Int) + 1 := by omega
      have := ih j (by omega)
      simp [patch, write, hne, this]

theorem patch_miss (A Q : Nat) (b : Int) (sym : Nat) (m : Int → Int) :
    ∀ (i : Nat) (x : Int), (∀ j : Nat, j < i → x ≠ b + 2 * (j : Int) + 1) →
      patch A Q b sym i m x = m x := by
  intro i
  induction i with
  | zero => intro x _; rfl
  | succ i ih =>
    intro x h
    have h1 : x ≠ b + 2 * (i : Int) + 1 := h i (by omega)
    have := ih x (fun j hj => h j (by omega))
    simp [patch, write, h1, this]

/-! Single-step facts in clean form. -/

theorem step_jmp' (pc : Int) (m : Int → Int) (h : m pc = 2) :
    WE.step ⟨pc, m⟩ = (.running, ⟨pc + 2 + m (pc + 1), m⟩) := by
  simp [WE.step, WE.decode, h]

theorem step_mov' (pc : Int) (m : Int → Int) (h : m pc = 1) :
    WE.step ⟨pc, m⟩ = (.running, ⟨pc + 3, write m (pc + 3 + m (pc + 1)) (m (pc + 2))⟩) := by
  simp [WE.step, WE.decode, h]

theorem step_hlt' (pc : Int) (m : Int → Int) (h : m pc = 3) :
    WE.step ⟨pc, m⟩ = (.halted, ⟨pc, m⟩) := by
  simp [WE.step, WE.decode, h]

/-! Handler words. -/

theorem hw_op {A Q : Nat} (M : Machine A Q) {q sym nx right q'} (i : Nat) (hi : i < Q)
    (ht : trans M q sym = some (nx, right, q')) : handlerWord M q sym (3 * i) = 1 := by
  have a1 : 3 * i < 3 * Q := by omega
  have a2 : 3 * i % 3 = 0 := by omega
  simp [handlerWord, ht, a1, a2]

theorem hw_rel {A Q : Nat} (M : Machine A Q) {q sym nx right q'} (i : Nat) (hi : i < Q)
    (ht : trans M q sym = some (nx, right, q')) :
    handlerWord M q sym (3 * i + 1) =
      (2 * (i : Int) + 1) - ((handlerAt A Q q sym : Int) + 3 * (i : Int) + 3) := by
  have a1 : 3 * i + 1 < 3 * Q := by omega
  have a2 : ¬ (3 * i + 1) % 3 = 0 := by omega
  have a3 : (3 * i + 1) % 3 = 1 := by omega
  have a4 : (3 * i + 1) / 3 = i := by omega
  simp [handlerWord, ht, a1, a2, a3, a4]

theorem hw_val {A Q : Nat} (M : Machine A Q) {q sym right q'} (nx : Fin A) (i : Nat) (hi : i < Q)
    (ht : trans M q sym = some (nx, right, q')) :
    handlerWord M q sym (3 * i + 2) = entryDisp A Q i nx.val := by
  have a1 : 3 * i + 2 < 3 * Q := by omega
  have a2 : ¬ (3 * i + 2) % 3 = 0 := by omega
  have a3 : ¬ (3 * i + 2) % 3 = 1 := by omega
  have a4 : (3 * i + 2) / 3 = i := by omega
  simp [handlerWord, ht, a1, a2, a3, a4]

theorem hw_jop {A Q : Nat} (M : Machine A Q) {q sym nx right q'}
    (ht : trans M q sym = some (nx, right, q')) : handlerWord M q sym (3 * Q) = 2 := by
  simp [handlerWord, ht]

theorem hw_jrel {A Q : Nat} (M : Machine A Q) {q sym nx} (right : Bool) (q' : Fin Q)
    (ht : trans M q sym = some (nx, right, q')) :
    handlerWord M q sym (3 * Q + 1) =
      (if right then (cellSize A Q : Int) else -(cellSize A Q : Int)) + 2 * (q'.val : Int)
        - ((handlerAt A Q q sym : Int) + 3 * (Q : Int) + 2) := by
  have a1 : ¬ 3 * Q + 1 < 3 * Q := by omega
  have a2 : ¬ 3 * Q + 1 = 3 * Q := by omega
  simp [handlerWord, ht, a1, a2]

theorem hw_hlt {A Q : Nat} (M : Machine A Q) {q sym}
    (ht : trans M q sym = none) : handlerWord M q sym 0 = 3 := by
  simp [handlerWord, ht]

/-! A word inside the handler of `(q, sym)` of cell `c`, seen through `i` entry rewrites. -/

theorem lay {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c x : Int) (j : Nat)
    (hj : j < cellSize A Q) (hx : x = c * (cellSize A Q : Int) + (j : Int)) :
    layout M tape x = cellWord M (tape c).val j := by
  subst hx; exact layout_at M tape c j hj

theorem patched_word {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c : Int)
    (q sym a' : Nat) (hq : q < Q) (hs : sym < A) (htape : (tape c).val = sym)
    (i : Nat) (hi : i ≤ Q) (k : Nat) (hk : k < handlerSize Q) (x : Int)
    (hx : x = c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + (k : Int)) :
    patch A Q (c * (cellSize A Q : Int)) a' i (layout M tape) x = handlerWord M q sym k := by
  have hh : 2 * Q ≤ handlerAt A Q q sym := by unfold handlerAt; omega
  have hend := handler_end_le (A := A) q sym k hq hs hk
  rw [patch_miss A Q _ a' (layout M tape) i x (fun j hj => by omega)]
  rw [lay M tape c x (handlerAt A Q q sym + k) hend (by push_cast; omega), htape]
  exact cellWord_handler M sym q sym k hq hs hk

/-- Entry: the jump at `2q` lands on the handler for the cell's symbol. -/
theorem entry_step {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c : Int) (q : Nat)
    (hq : q < Q) :
    WE.step ⟨c * (cellSize A Q : Int) + 2 * (q : Int), layout M tape⟩ =
      (.running, ⟨c * (cellSize A Q : Int) + (handlerAt A Q q (tape c).val : Int), layout M tape⟩) := by
  have hS : 2 * q + 1 < cellSize A Q := by unfold cellSize; omega
  have h0 := lay M tape c (c * (cellSize A Q : Int) + 2 * (q : Int)) (2 * q) (by omega)
    (by push_cast; omega)
  have h1 := lay M tape c (c * (cellSize A Q : Int) + 2 * (q : Int) + 1) (2 * q + 1) hS
    (by push_cast; omega)
  rw [cellWord_entry_op M _ q hq] at h0
  rw [cellWord_entry_disp M _ q hq] at h1
  rw [step_jmp' _ _ h0, h1]
  have e : c * (cellSize A Q : Int) + 2 * (q : Int) + 2 + entryDisp A Q q (tape c).val
      = c * (cellSize A Q : Int) + (handlerAt A Q q (tape c).val : Int) := by
    unfold entryDisp; omega
  rw [e]


/-- One of the `Q` stores of a handler: it rewrites the displacement of entry `i`. -/
theorem mov_step {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c : Int)
    (q sym : Nat) (hq : q < Q) (hs : sym < A) (htape : (tape c).val = sym)
    (nx : Fin A) (right : Bool) (q' : Fin Q) (ht : trans M q sym = some (nx, right, q'))
    (i : Nat) (hi : i < Q) :
    WE.step ⟨c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * (i : Int),
        patch A Q (c * (cellSize A Q : Int)) nx.val i (layout M tape)⟩ =
      (.running, ⟨c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * ((i + 1 : Nat) : Int),
        patch A Q (c * (cellSize A Q : Int)) nx.val (i + 1) (layout M tape)⟩) := by
  have w0 := patched_word M tape c q sym nx.val hq hs htape i (by omega) (3 * i)
    (by unfold handlerSize; omega)
    (c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * (i : Int)) (by push_cast; omega)
  have w1 := patched_word M tape c q sym nx.val hq hs htape i (by omega) (3 * i + 1)
    (by unfold handlerSize; omega)
    (c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * (i : Int) + 1) (by push_cast; omega)
  have w2 := patched_word M tape c q sym nx.val hq hs htape i (by omega) (3 * i + 2)
    (by unfold handlerSize; omega)
    (c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * (i : Int) + 2) (by push_cast; omega)
  rw [hw_op M i hi ht] at w0
  rw [hw_rel M i hi ht] at w1
  rw [hw_val M nx i hi ht] at w2
  rw [step_mov' _ _ w0, w1, w2]
  have e : c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * (i : Int) + 3
      + ((2 * (i : Int) + 1) - ((handlerAt A Q q sym : Int) + 3 * (i : Int) + 3))
      = c * (cellSize A Q : Int) + 2 * (i : Int) + 1 := by omega
  have e2 : c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * (i : Int) + 3
      = c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * ((i + 1 : Nat) : Int) := by
    push_cast; omega
  rw [e, e2]
  rfl

theorem mov_loop {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c : Int)
    (q sym : Nat) (hq : q < Q) (hs : sym < A) (htape : (tape c).val = sym)
    (nx : Fin A) (right : Bool) (q' : Fin Q) (ht : trans M q sym = some (nx, right, q')) :
    ∀ i, i ≤ Q →
      WE.run i ⟨c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int), layout M tape⟩ =
        (.running, ⟨c * (cellSize A Q : Int) + (handlerAt A Q q sym : Int) + 3 * (i : Int),
          patch A Q (c * (cellSize A Q : Int)) nx.val i (layout M tape)⟩) := by
  intro i
  induction i with
  | zero => intro _; simp [WE.run, patch]
  | succ i ih =>
    intro hi
    rw [WE.run_succ_right, ih (by omega)]
    exact mov_step M tape c q sym hq hs htape nx right q' ht i (by omega)

/-- After all `Q` stores the patched image is the image of the rewritten tape. -/
theorem patch_eq_layout_write {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c : Int)
    (a' : Fin A) :
    patch A Q (c * (cellSize A Q : Int)) a'.val Q (layout M tape) = layout M (write tape c a') := by
  funext x
  by_cases hex : ∃ j : Nat, j < Q ∧ x = c * (cellSize A Q : Int) + 2 * (j : Int) + 1
  · obtain ⟨j, hj, hxj⟩ := hex
    subst hxj
    rw [patch_hit A Q _ a'.val _ Q j hj]
    have hS : 2 * j + 1 < cellSize A Q := by unfold cellSize; omega
    rw [lay M (write tape c a') c _ (2 * j + 1) hS (by push_cast; omega)]
    simp only [read_write_same]
    exact (cellWord_entry_disp M a'.val j hj).symm
  · have hmiss : ∀ j : Nat, j < Q → x ≠ c * (cellSize A Q : Int) + 2 * (j : Int) + 1 :=
      fun j hj h => hex ⟨j, hj, h⟩
    rw [patch_miss A Q _ a'.val (layout M tape) Q x hmiss]
    unfold layout
    by_cases hd : x / (cellSize A Q : Int) = c
    · rw [hd]
      simp only [read_write_same]
      apply cellWord_indep
      rintro ⟨hr1, hr2⟩
      apply hex
      have hSpos : (0 : Int) < (cellSize A Q : Int) := by unfold cellSize; omega
      have key := Int.mul_ediv_add_emod x (cellSize A Q : Int)
      have hnn := Int.emod_nonneg x (Int.ne_of_gt hSpos)
      rw [hd, Int.mul_comm] at key
      generalize x % (cellSize A Q : Int) = r at *
      refine ⟨r.toNat / 2, by omega, by omega⟩
    · simp [write, hd]

/-- C02 core: a state with a transition takes exactly `Q + 2` steps to realise it. -/
theorem cell_step_some {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c : Int)
    (q : Fin Q) (nx : Fin A) (right : Bool) (q' : Fin Q)
    (ht : M.transition q (tape c) = some (nx, right, q')) :
    WE.run (Q + 2) ⟨c * (cellSize A Q : Int) + 2 * (q.val : Int), layout M tape⟩ =
      (.running, ⟨(if right then c + 1 else c - 1) * (cellSize A Q : Int) + 2 * (q'.val : Int),
        layout M (write tape c nx)⟩) := by
  have ht' : trans M q.val (tape c).val = some (nx, right, q') := by
    simp [trans, q.2, (tape c).2, ht]
  have r1 : WE.run (1 + Q) ⟨c * (cellSize A Q : Int) + 2 * (q.val : Int), layout M tape⟩ =
      (.running, ⟨c * (cellSize A Q : Int) + (handlerAt A Q q.val (tape c).val : Int)
        + 3 * (Q : Int), patch A Q (c * (cellSize A Q : Int)) nx.val Q (layout M tape)⟩) := by
    rw [WE.run_add, WE.run_one, entry_step M tape c q.val q.2]
    exact mov_loop M tape c q.val (tape c).val q.2 (tape c).2 rfl nx right q' ht' Q (Nat.le_refl _)
  have w0 := patched_word M tape c q.val (tape c).val nx.val q.2 (tape c).2 rfl Q (Nat.le_refl _) (3 * Q)
    (by unfold handlerSize; omega)
    (c * (cellSize A Q : Int) + (handlerAt A Q q.val (tape c).val : Int) + 3 * (Q : Int))
    (by push_cast; omega)
  have w1 := patched_word M tape c q.val (tape c).val nx.val q.2 (tape c).2 rfl Q (Nat.le_refl _) (3 * Q + 1)
    (by unfold handlerSize; omega)
    (c * (cellSize A Q : Int) + (handlerAt A Q q.val (tape c).val : Int) + 3 * (Q : Int) + 1)
    (by push_cast; omega)
  rw [hw_jop M ht'] at w0
  rw [hw_jrel M right q' ht'] at w1
  have e : Q + 2 = 1 + Q + 1 := by omega
  rw [e, WE.run_succ_right, r1]
  show WE.step _ = _
  rw [step_jmp' _ _ w0, w1, patch_eq_layout_write]
  have hmul : (if right then c + 1 else c - 1) * (cellSize A Q : Int) =
      c * (cellSize A Q : Int) + (if right then (cellSize A Q : Int) else -(cellSize A Q : Int)) := by
    cases right <;> simp [Int.add_mul, Int.sub_mul]
    omega
  rw [hmul]
  have e2 : c * (cellSize A Q : Int) + (handlerAt A Q q.val (tape c).val : Int) + 3 * (Q : Int) + 2
      + ((if right then (cellSize A Q : Int) else -(cellSize A Q : Int)) + 2 * (q'.val : Int)
        - ((handlerAt A Q q.val (tape c).val : Int) + 3 * (Q : Int) + 2))
      = c * (cellSize A Q : Int) + (if right then (cellSize A Q : Int) else -(cellSize A Q : Int))
        + 2 * (q'.val : Int) := by omega
  rw [e2]

/-- A missing transition: the entry jump and the halt, two steps. -/
theorem cell_step_none {A Q : Nat} (M : Machine A Q) (tape : Int → Fin A) (c : Int)
    (q : Fin Q) (ht : M.transition q (tape c) = none) :
    WE.run 2 ⟨c * (cellSize A Q : Int) + 2 * (q.val : Int), layout M tape⟩ =
      (.halted, ⟨c * (cellSize A Q : Int) + (handlerAt A Q q.val (tape c).val : Int),
        layout M tape⟩) := by
  have ht' : trans M q.val (tape c).val = none := by
    simp [trans, q.2, (tape c).2, ht]
  have hh : 2 * Q ≤ handlerAt A Q q.val (tape c).val := by unfold handlerAt; omega
  have hend := handler_end_le (A := A) q.val (tape c).val 0 q.2 (tape c).2
    (by unfold handlerSize; omega)
  have w0 := lay M tape c (c * (cellSize A Q : Int) + (handlerAt A Q q.val (tape c).val : Int))
    (handlerAt A Q q.val (tape c).val + 0) hend (by push_cast; omega)
  rw [cellWord_handler M _ q.val (tape c).val 0 q.2 (tape c).2 (by unfold handlerSize; omega),
    hw_hlt M ht'] at w0
  have r1 : WE.run 1 ⟨c * (cellSize A Q : Int) + 2 * (q.val : Int), layout M tape⟩ =
      (.running, ⟨c * (cellSize A Q : Int) + (handlerAt A Q q.val (tape c).val : Int),
        layout M tape⟩) := by
    rw [WE.run_one]; exact entry_step M tape c q.val q.2
  rw [WE.run_succ_right, r1]
  show WE.step _ = _
  exact step_hlt' _ _ w0

end WriteExecute.Universal
