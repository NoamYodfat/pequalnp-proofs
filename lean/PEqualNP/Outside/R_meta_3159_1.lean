import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding in
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_3159_1
    (complete : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      (∀ r ∈ rows, r < 2^n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      FormulaSat (enc n s g rows))
    (impossible :
      ¬ FormulaSat (enc 10 14
        (fun r => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => r.testBit (e / 10) && r.testBit (e % 10)))
        ((List.range 512).map fun r => if r.testBit 0 then r else r + 512)))
    (single : ∀ (b : ℕ) (op : Fin b → Bool) (l r : Fin b → ℕ × Bool)
      (phase : Bool) (paid : Finset ℕ) (w : (Fin 9 → Bool) → ℕ → Bool),
      0 < b → paid.card = 1 → b ≤ 13 →
      (∀ j, (l j).1 < 10 + j.val ∧ (r j).1 < 10 + j.val) →
      (∀ i : Fin 9, ∃ j, (l j).1 = i.val ∨ (r j).1 = i.val) →
      (∀ i, i ∈ paid ↔ i ≠ 0 ∧ i ≠ 9 ∧
        ((phase = true ∧ i = 9 + b) ∨ ∃ j, l j = (i,true) ∨ r j = (i,true))) →
      (∀ x (i : Fin 9), w x i.val = x i) → (∀ x, w x 9 = false) →
      (∀ x j, let v := fun p : ℕ × Bool => w x p.1 ^^ p.2
        w x (10+j.val) = if op j then v (l j) && v (r j) else v (l j) || v (r j)) →
      ∃ x : Fin 9 → Bool, (w x (9+b) ^^ phase) ≠
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (0 : ℕ) < x1 →     x6.card ≤ (3 : ℕ) →       x1 + x6.card ≤ (14 : ℕ) →         x6.card ≤ (1 : ℕ) →           (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) →             (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) →               (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (x5 = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) →                   (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) →                     (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                         have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2;                         x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                       ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ))) := by
  intro n op l r phase paid w hb hc3 hcost hc1 hback hcover hpaid raw zero step
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc1 with h0 | h1
  swap
  · exact single n op l r phase paid w hb h1 (by omega) hback hcover hpaid raw zero step
  have hpe : paid = ∅ := Finset.card_eq_zero.mp h0
  have nopaid : ∀ i, i ∉ paid := by simp [hpe]
  have litok : ∀ (j : Fin n) (p : ℕ × Bool), (p = l j ∨ p = r j) → p.2 = true →
      p.1 = 0 ∨ p.1 = 9 := by
    intro j p hp ht
    by_contra hne
    push Not at hne
    apply nopaid p.1
    rw [hpaid]
    refine ⟨hne.1, hne.2, Or.inr ⟨j, ?_⟩⟩
    rcases hp with rfl | rfl
    · exact Or.inl (Prod.ext rfl ht)
    · exact Or.inr (Prod.ext rfl ht)
  have hph : phase = false := by
    by_contra hp
    simp only [Bool.not_eq_false] at hp
    apply nopaid (9 + n)
    rw [hpaid]
    exact ⟨by omega, by omega, Or.inl ⟨hp, rfl⟩⟩
  let src : ℕ × Bool → ℕ := fun p => if p.2 then 9 else p.1
  let opnd : ℕ × Bool → List ℕ := fun p => if p.1 = 9 then [] else [src p]
  let gateOf : Bool → ℕ × Bool → ℕ × Bool → Gate := fun o a c =>
    if o then
      (if (a.1 = 9 ∧ a.2 = false) ∨ (c.1 = 9 ∧ c.2 = false) then ⟨GateOp.or, []⟩
        else ⟨GateOp.and, opnd a ++ opnd c⟩)
    else
      (if (a.1 = 9 ∧ a.2 = true) ∨ (c.1 = 9 ∧ c.2 = true) then ⟨GateOp.and, []⟩
        else ⟨GateOp.or, opnd a ++ opnd c⟩)
  let G : ℕ → Gate := fun j =>
    if h : j < n then gateOf (op ⟨j, h⟩) (l ⟨j, h⟩) (r ⟨j, h⟩) else ⟨GateOp.or, []⟩
  let C : Circuit := ⟨(List.range n).map G, 9 + n⟩
  have gateOk : ∀ o a c, (gateOf o a c).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (gateOf o a c).inputs.length ≤ 2 := by
    intro o a c
    simp only [gateOf, opnd]
    split_ifs <;> simp
  have gateEval : ∀ (o : Bool) (a c : ℕ × Bool) (get : ℕ → Bool) (va vc : Bool),
      (a.1 = 9 → va = a.2) → (a.1 ≠ 9 → get (src a) = va) →
      (c.1 = 9 → vc = c.2) → (c.1 ≠ 9 → get (src c) = vc) →
      (gateOf o a c).op.eval ((gateOf o a c).inputs.map get) =
        (if o then va && vc else va || vc) := by
    intro o a c get va vc h1 h2 h3 h4
    obtain ⟨a1, a2⟩ := a
    obtain ⟨c1, c2⟩ := c
    simp only at h1 h2 h3 h4
    by_cases ha : a1 = 9 <;> by_cases hc : c1 = 9
    · subst ha hc
      rw [h1 rfl, h3 rfl]
      cases o <;> cases a2 <;> cases c2 <;> simp [gateOf, opnd, GateOp.eval]
    · subst ha
      rw [h1 rfl, ← h4 hc]
      cases o <;> cases a2 <;> simp [gateOf, opnd, hc, GateOp.eval]
    · subst hc
      rw [h3 rfl, ← h2 ha]
      cases o <;> cases c2 <;> simp [gateOf, opnd, ha, GateOp.eval]
    · rw [← h2 ha, ← h4 hc]
      cases o <;> simp [gateOf, opnd, ha, hc, GateOp.eval]
  have hmono : Monotone2 C := by
    intro g hg
    simp only [C, List.mem_map, List.mem_range] at hg
    obtain ⟨j, hj, rfl⟩ := hg
    simp only [G, dif_pos hj]
    exact gateOk _ _ _
  have hsize : C.size ≤ 14 := by
    simp only [C, Circuit.size, List.length_map, List.length_range]
    omega
  let inp : ℕ → List Bool := fun ρ => List.ofFn fun i : Fin 10 => ρ.testBit i.val
  let xr : ℕ → Fin 9 → Bool := fun ρ i => ρ.testBit i.val
  let wv : ℕ → ℕ → Bool := fun ρ i =>
    if i < 9 then ρ.testBit i else if i = 9 then !ρ.testBit 0 else w (xr ρ) i
  have snoc : ∀ (gs : List Gate) (g : Gate) (x : List Bool),
      (Circuit.mk (gs ++ [g]) 0).wires x =
        (Circuit.mk gs 0).wires x ++
          [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
    intro gs g x
    simp [Circuit.wires, List.foldl_append]
  have key : ∀ ρ : ℕ, ρ.testBit 9 = !ρ.testBit 0 → ∀ k, k ≤ n →
      ((Circuit.mk ((List.range k).map G) 0).wires (inp ρ)).length = 10 + k ∧
      ∀ i < 10 + k, ((Circuit.mk ((List.range k).map G) 0).wires (inp ρ)).getD i false =
        wv ρ i := by
    intro ρ h9 k
    induction k with
    | zero =>
      intro _
      refine ⟨by simp [Circuit.wires, inp], ?_⟩
      intro i hi
      simp only [List.range_zero, List.map_nil, Circuit.wires, List.foldl_nil, inp, wv]
      simp only [Nat.add_zero] at hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp only [hi, List.ofFnNthVal, dite_true, Option.getD_some]
      split_ifs with h1 h2
      · rfl
      · subst h2; exact h9
      · omega
    | succ k ih =>
      intro hk
      obtain ⟨hlen, hval⟩ := ih (by omega)
      rw [List.range_succ, List.map_append, List.map_singleton, snoc]
      refine ⟨by simp [hlen]; omega, ?_⟩
      intro i hi
      rcases Nat.lt_or_ge i (10 + k) with hlt | hge
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hval i hlt
      · have hi' : i = 10 + k := by omega
        subst hi'
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp only [hlen, Nat.sub_self, List.getD_cons_zero]
        have hkn : k < n := by omega
        have stp := step (xr ρ) ⟨k, hkn⟩
        simp only at stp
        have wvk : wv ρ (10 + k) = w (xr ρ) (10 + k) := by
          simp only [wv]
          rw [if_neg (by omega), if_neg (by omega)]
        rw [wvk, stp]
        simp only [G, dif_pos hkn]
        have operand : ∀ p : ℕ × Bool, (p = l ⟨k, hkn⟩ ∨ p = r ⟨k, hkn⟩) →
            (p.1 = 9 → (w (xr ρ) p.1 ^^ p.2) = p.2) ∧
            (p.1 ≠ 9 → ((Circuit.mk ((List.range k).map G) 0).wires (inp ρ)).getD (src p) false =
              (w (xr ρ) p.1 ^^ p.2)) := by
          intro p hp
          have hlt : p.1 < 10 + k := by
            rcases hp with rfl | rfl
            · exact (hback ⟨k, hkn⟩).1
            · exact (hback ⟨k, hkn⟩).2
          refine ⟨fun h => by rw [h, zero]; simp, fun hne => ?_⟩
          by_cases ht : p.2 = true
          · have h0' : p.1 = 0 := by
              rcases litok ⟨k, hkn⟩ p hp ht with h | h
              · exact h
              · exact absurd h hne
            have hs : src p = 9 := by simp [src, ht]
            rw [hs, hval 9 (by omega), ht, h0']
            have := raw (xr ρ) ⟨0, by norm_num⟩
            simp only at this
            simp [wv, this, xr]
          · have hf : p.2 = false := by simpa using ht
            have hs : src p = p.1 := by simp [src, hf]
            rw [hs, hval p.1 hlt, hf, Bool.xor_false]
            by_cases h9' : p.1 < 9
            · have := raw (xr ρ) ⟨p.1, h9'⟩
              simp only at this
              simp [wv, h9', this, xr]
            · simp only [wv]
              rw [if_neg h9', if_neg hne]
        obtain ⟨ha1, ha2⟩ := operand (l ⟨k, hkn⟩) (Or.inl rfl)
        obtain ⟨hc1', hc2⟩ := operand (r ⟨k, hkn⟩) (Or.inr rfl)
        exact gateEval _ _ _ _ _ _ ha1 ha2 hc1' hc2
  by_contra hall
  push Not at hall
  apply impossible
  have hrows : ∀ ρ ∈ ((List.range 512).map fun r => if r.testBit 0 then r else r + 512),
      ρ < 2 ^ 10 ∧ ρ.testBit 9 = !ρ.testBit 0 := by
    have hall' : ((List.range 512).map fun r => if r.testBit 0 then r else r + 512).all
        (fun ρ => decide (ρ < 2 ^ 10) && (ρ.testBit 9 == !ρ.testBit 0)) = true := by
      decide +kernel
    intro ρ hρ
    have := List.all_eq_true.mp hall' ρ hρ
    simpa using this
  apply complete 10 14 _ _ C (fun ρ hρ => (hrows ρ hρ).1) hmono hsize
  intro ρ hρ
  have h9 := (hrows ρ hρ).2
  obtain ⟨hlen, hval⟩ := key ρ h9 n le_rfl
  have hev : C.eval (inp ρ) = w (xr ρ) (9 + n) := by
    have := hval (9 + n) (by omega)
    simp only [wv] at this
    rw [if_neg (by omega), if_neg (by omega)] at this
    exact this
  change C.eval (inp ρ) = _
  rw [hev]
  have := hall (xr ρ)
  rw [hph, Bool.xor_false] at this
  rw [this]
  simp only [List.any_cons, List.any_nil, xr]
  rfl
