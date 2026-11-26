import Proofs.Defs

set_option maxHeartbeats 400000

@[reducible] def SuStp {X : Type*} [LinearOrder X] (u v : X → Bool) (x : X) : Prop :=
  u x = false ∧ v x = true ∧ ∀ y, x < y → u y = v y

@[reducible] def suVlt {X : Type*} [LinearOrder X] (u v : X → Bool) : Prop :=
  ∃ x, SuStp u v x

@[reducible] def SuCol0 {X : Type*} [LinearOrder X] (χ χ' : Finset X → Fin 2)
    (d1 d2 d3 : X) : Prop :=
  (d1 < d2 ∧ d3 < d2) ∨ (d1 < d2 ∧ d2 < d3 ∧ χ {d1, d2, d3} = 0) ∨
    (d2 < d1 ∧ d3 < d2 ∧ χ' {d3, d2, d1} = 0)

@[reducible] def SuRep {X : Type*} [LinearOrder X] [Fintype X] (A : Finset (X → Bool))
    (a b c d : X → Bool) (x y w : X) : Prop :=
  A = {a, b, c, d} ∧ SuStp a b x ∧ SuStp b c y ∧ SuStp c d w

noncomputable def suPsi {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2)
    (A : Finset (X → Bool)) : Fin 2 := by
  classical
  exact if ∃ a b c d : X → Bool, ∃ x y w : X, SuRep A a b c d x y w ∧ SuCol0 χ χ' x y w
    then 0 else 1

lemma su_bool_ne : ∀ a b : Bool, a ≠ b → (a = false ∧ b = true) ∨ (a = true ∧ b = false) := by
  decide

lemma su_bool_cases : ∀ b : Bool, b = false ∨ b = true := by decide

lemma su_fin2_cases : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide

lemma su_irrefl {X : Type*} [LinearOrder X] {u : X → Bool} {x : X} (h : SuStp u u x) :
    False := by
  have h1 := h.1
  have h2 := h.2.1
  rw [h1] at h2
  exact absurd h2 (by decide)

lemma su_unique {X : Type*} [LinearOrder X] {u v : X → Bool} {x y : X}
    (hx : SuStp u v x) (hy : SuStp u v y) : x = y := by
  rcases lt_trichotomy x y with h | h | h
  · exfalso
    have t := hx.2.2 y h
    rw [hy.1, hy.2.1] at t
    exact absurd t (by decide)
  · exact h
  · exfalso
    have t := hy.2.2 x h
    rw [hx.1, hx.2.1] at t
    exact absurd t (by decide)

lemma su_asymm {X : Type*} [LinearOrder X] {u v : X → Bool} {x y : X}
    (hx : SuStp u v x) (hy : SuStp v u y) : False := by
  rcases lt_trichotomy x y with h | h | h
  · have t := hx.2.2 y h
    rw [hy.2.1, hy.1] at t
    exact absurd t (by decide)
  · have t := hy.2.1
    rw [← h, hx.1] at t
    exact absurd t (by decide)
  · have t := hy.2.2 x h
    rw [hx.2.1, hx.1] at t
    exact absurd t (by decide)

lemma su_tri {X : Type*} [LinearOrder X] {u v w : X → Bool} {x y : X}
    (hx : SuStp u v x) (hy : SuStp v w y) :
    (x < y ∧ SuStp u w y) ∨ (y < x ∧ SuStp u w x) := by
  rcases lt_trichotomy x y with h | h | h
  · left
    refine ⟨h, ?_, hy.2.1, fun z hz => ?_⟩
    · rw [hx.2.2 y h]; exact hy.1
    · rw [hx.2.2 z (lt_trans h hz)]; exact hy.2.2 z hz
  · exfalso
    have h1 := hx.2.1
    have h2 := hy.1
    rw [← h, h1] at h2
    exact absurd h2 (by decide)
  · right
    refine ⟨h, hx.1, ?_, fun z hz => ?_⟩
    · rw [← hy.2.2 x h]; exact hx.2.1
    · rw [hx.2.2 z hz]; exact hy.2.2 z (lt_trans h hz)

lemma su_ne {X : Type*} [LinearOrder X] {u v : X → Bool} {x : X} (hx : SuStp u v x) :
    u ≠ v := by
  intro h
  rw [h] at hx
  exact su_irrefl hx

lemma su_vlt_asymm {X : Type*} [LinearOrder X] (u v : X → Bool) (h1 : suVlt u v)
    (h2 : suVlt v u) : False := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  exact su_asymm hx hy

lemma su_vlt_trans {X : Type*} [LinearOrder X] (u v w : X → Bool) (h1 : suVlt u v)
    (h2 : suVlt v w) : suVlt u w := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  rcases su_tri hx hy with ⟨_, h⟩ | ⟨_, h⟩
  · exact ⟨y, h⟩
  · exact ⟨x, h⟩

lemma su_total {X : Type*} [LinearOrder X] [Fintype X] {u v : X → Bool} (h : u ≠ v) :
    ∃ x, SuStp u v x ∨ SuStp v u x := by
  obtain ⟨x0, hx0⟩ := Function.ne_iff.mp h
  have hne : (Finset.univ.filter (fun x : X => u x ≠ v x)).Nonempty :=
    ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩⟩
  obtain ⟨x, hxS, hmax⟩ := Finset.exists_max_image _ (fun x : X => x) hne
  have hx : u x ≠ v x := (Finset.mem_filter.mp hxS).2
  have hab : ∀ y, x < y → u y = v y := by
    intro y hy
    by_contra hc
    have h1 : y ≤ x := hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    exact absurd hy (not_lt.mpr h1)
  refine ⟨x, ?_⟩
  rcases su_bool_ne _ _ hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; exact ⟨h1, h2, hab⟩
  · right; exact ⟨h2, h1, fun y hy => (hab y hy).symm⟩

lemma su_real_up {X : Type*} [LinearOrder X] {q b c : X → Bool} {x y : X}
    (hb : SuStp q b x) (hc : SuStp q c y) (h : x < y) : SuStp b c y := by
  refine ⟨?_, hc.2.1, fun z hz => ?_⟩
  · rw [← hb.2.2 y h]; exact hc.1
  · rw [← hb.2.2 z (lt_trans h hz)]; exact hc.2.2 z hz

lemma su_real_down {X : Type*} [LinearOrder X] {a c q : X → Bool} {x y : X}
    (ha : SuStp a q x) (hc : SuStp c q y) (h : x < y) : SuStp c a y := by
  refine ⟨hc.1, ?_, fun z hz => ?_⟩
  · rw [ha.2.2 y h]; exact hc.2.1
  · rw [ha.2.2 z (lt_trans h hz)]; exact hc.2.2 z hz

lemma su_sort3 {X : Type*} [LinearOrder X] (A : Finset X) (h : A.card = 3) :
    ∃ x y w, x < y ∧ y < w ∧ A = {x, y, w} := by
  obtain ⟨x, y, w, hxy, hxw, hyw, hA⟩ := Finset.card_eq_three.mp h
  rcases lt_or_gt_of_ne hxy with h1 | h1
  · rcases lt_or_gt_of_ne hyw with h3 | h3
    · exact ⟨x, y, w, h1, h3, hA⟩
    · rcases lt_or_gt_of_ne hxw with h2 | h2
      · refine ⟨x, w, y, h2, h3, ?_⟩
        rw [hA]; ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨w, x, y, h2, h1, ?_⟩
        rw [hA]; ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
  · rcases lt_or_gt_of_ne hyw with h3 | h3
    · rcases lt_or_gt_of_ne hxw with h2 | h2
      · refine ⟨y, x, w, h1, h2, ?_⟩
        rw [hA]; ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      · refine ⟨y, w, x, h3, h2, ?_⟩
        rw [hA]; ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
    · refine ⟨w, y, x, h3, h1, ?_⟩
      rw [hA]; ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto

lemma su_clique_bound {X : Type*} [LinearOrder X] (χ : Finset X → Fin 2) (i : Fin 2) (n : ℕ)
    (hχ : Solon.NoMono χ 3 n i) (T : Finset X)
    (hT : ∀ x ∈ T, ∀ y ∈ T, ∀ w ∈ T, x < y → y < w → χ {x, y, w} = i) : T.card < n := by
  by_contra hcon
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq (show n ≤ T.card by omega)
  obtain ⟨A, hA, hne⟩ := hχ S hSc
  obtain ⟨hAS, hAc⟩ := Finset.mem_powersetCard.mp hA
  obtain ⟨x, y, w, hxy, hyw, hAe⟩ := su_sort3 A hAc
  apply hne
  have mx : x ∈ T := hS (hAS (by rw [hAe]; simp))
  have my : y ∈ T := hS (hAS (by rw [hAe]; simp))
  have mw : w ∈ T := hS (hAS (by rw [hAe]; simp))
  rw [hAe]
  exact hT x mx y my w mw hxy hyw

lemma su_up_clique {X : Type*} [LinearOrder X] (K : Finset (X → Bool)) (T : Finset X)
    (q : X → Bool) (hq : q ∈ K) (hT : ∀ x ∈ T, ∃ b ∈ K, SuStp q b x) (x y w : X)
    (hx : x ∈ T) (hy : y ∈ T) (hw : w ∈ T) (hxy : x < y) (hyw : y < w) :
    ∃ a ∈ K, ∃ b ∈ K, ∃ c ∈ K, ∃ d ∈ K, SuStp a b x ∧ SuStp b c y ∧ SuStp c d w := by
  obtain ⟨b, hb, hbx⟩ := hT x hx
  obtain ⟨c, hc, hcy⟩ := hT y hy
  obtain ⟨d, hd, hdw⟩ := hT w hw
  exact ⟨q, hq, b, hb, c, hc, d, hd, hbx, su_real_up hbx hcy hxy, su_real_up hcy hdw hyw⟩

lemma su_down_clique {X : Type*} [LinearOrder X] (K : Finset (X → Bool)) (T' : Finset X)
    (q' : X → Bool) (hq' : q' ∈ K) (hT' : ∀ x ∈ T', ∃ a ∈ K, SuStp a q' x) (x y w : X)
    (hx : x ∈ T') (hy : y ∈ T') (hw : w ∈ T') (hxy : x < y) (hyw : y < w) :
    ∃ a ∈ K, ∃ b ∈ K, ∃ c ∈ K, ∃ d ∈ K, SuStp a b w ∧ SuStp b c y ∧ SuStp c d x := by
  obtain ⟨a, ha, hax⟩ := hT' x hx
  obtain ⟨b, hb, hby⟩ := hT' y hy
  obtain ⟨c, hc, hcw⟩ := hT' w hw
  exact ⟨c, hc, b, hb, a, ha, q', hq', su_real_down hby hcw hyw, su_real_down hax hby hxy, hax⟩

lemma su_chain4_unique {α : Type*} [DecidableEq α] (r : α → α → Prop)
    (asym : ∀ a b, r a b → r b a → False) (tr : ∀ a b c, r a b → r b c → r a c)
    (a b c d a' b' c' d' : α) (h1 : r a b) (h2 : r b c) (h3 : r c d)
    (h1' : r a' b') (h2' : r b' c') (h3' : r c' d')
    (h : ({a, b, c, d} : Finset α) = {a', b', c', d'}) :
    a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  have irr : ∀ x, ¬ r x x := fun x hx => asym x x hx hx
  have hac := tr _ _ _ h1 h2
  have had := tr _ _ _ hac h3
  have hbd := tr _ _ _ h2 h3
  have hac' := tr _ _ _ h1' h2'
  have had' := tr _ _ _ hac' h3'
  have hbd' := tr _ _ _ h2' h3'
  have mem : ∀ v, v ∈ ({a, b, c, d} : Finset α) ↔ (v = a ∨ v = b ∨ v = c ∨ v = d) := by
    intro v
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have mem' : ∀ v, v ∈ ({a', b', c', d'} : Finset α) ↔
      (v = a' ∨ v = b' ∨ v = c' ∨ v = d') := by
    intro v
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have ma : a = a' ∨ a = b' ∨ a = c' ∨ a = d' :=
    (mem' a).mp (by rw [← h]; exact (mem a).mpr (Or.inl rfl))
  have mb : b = a' ∨ b = b' ∨ b = c' ∨ b = d' :=
    (mem' b).mp (by rw [← h]; exact (mem b).mpr (Or.inr (Or.inl rfl)))
  have mc : c = a' ∨ c = b' ∨ c = c' ∨ c = d' :=
    (mem' c).mp (by rw [← h]; exact (mem c).mpr (Or.inr (Or.inr (Or.inl rfl))))
  have md : d = a' ∨ d = b' ∨ d = c' ∨ d = d' :=
    (mem' d).mp (by rw [← h]; exact (mem d).mpr (Or.inr (Or.inr (Or.inr rfl))))
  have ma' : a' = a ∨ a' = b ∨ a' = c ∨ a' = d :=
    (mem a').mp (by rw [h]; exact (mem' a').mpr (Or.inl rfl))
  have mb' : b' = a ∨ b' = b ∨ b' = c ∨ b' = d :=
    (mem b').mp (by rw [h]; exact (mem' b').mpr (Or.inr (Or.inl rfl)))
  have md' : d' = a ∨ d' = b ∨ d' = c ∨ d' = d :=
    (mem d').mp (by rw [h]; exact (mem' d').mpr (Or.inr (Or.inr (Or.inr rfl))))
  have haa : a = a' := by
    by_contra hne
    have k1 : r a' a := by
      rcases ma with e | e | e | e
      · exact absurd e hne
      · rw [e]; exact h1'
      · rw [e]; exact hac'
      · rw [e]; exact had'
    have k2 : r a a' := by
      rcases ma' with e | e | e | e
      · exact absurd e.symm hne
      · rw [e]; exact h1
      · rw [e]; exact hac
      · rw [e]; exact had
    exact asym _ _ k1 k2
  have hdd : d = d' := by
    by_contra hne
    have k1 : r d d' := by
      rcases md with e | e | e | e
      · rw [e]; exact had'
      · rw [e]; exact hbd'
      · rw [e]; exact h3'
      · exact absurd e hne
    have k2 : r d' d := by
      rcases md' with e | e | e | e
      · rw [e]; exact had
      · rw [e]; exact hbd
      · rw [e]; exact h3
      · exact absurd e.symm hne
    exact asym _ _ k1 k2
  have hbb : b = b' := by
    rcases mb with e | e | e | e
    · exfalso
      have t := h1
      rw [e, ← haa] at t
      exact irr _ t
    · exact e
    · rcases mb' with f | f | f | f
      · exfalso
        have t := h1'
        rw [f, ← haa] at t
        exact irr _ t
      · exact f.symm
      · exfalso
        have t := h2'
        rw [f, ← e] at t
        exact asym _ _ h2 t
      · exfalso
        have t := hbd'
        rw [f, ← hdd] at t
        exact irr _ t
    · exfalso
      have t := hbd
      rw [e, ← hdd] at t
      exact irr _ t
  have hcc : c = c' := by
    rcases mc with e | e | e | e
    · exfalso
      have t := hac
      rw [e, ← haa] at t
      exact irr _ t
    · exfalso
      have t := h2
      rw [e, ← hbb] at t
      exact irr _ t
    · exact e
    · exfalso
      have t := h3
      rw [e, ← hdd] at t
      exact irr _ t
  exact ⟨haa, hbb, hcc, hdd⟩

lemma su_chain_card {X : Type*} [LinearOrder X] [Fintype X] {a b c d : X → Bool} {x y w : X}
    (hx : SuStp a b x) (hy : SuStp b c y) (hw : SuStp c d w) :
    ({a, b, c, d} : Finset (X → Bool)).card = 4 := by
  have hab := su_ne hx
  have hbc := su_ne hy
  have hcd := su_ne hw
  have hac : a ≠ c := by
    rcases su_tri hx hy with ⟨_, h⟩ | ⟨_, h⟩ <;> exact su_ne h
  have hbd : b ≠ d := by
    rcases su_tri hy hw with ⟨_, h⟩ | ⟨_, h⟩ <;> exact su_ne h
  have had : a ≠ d := by
    rcases su_tri hx hy with ⟨_, h⟩ | ⟨_, h⟩
    · rcases su_tri h hw with ⟨_, h'⟩ | ⟨_, h'⟩ <;> exact su_ne h'
    · rcases su_tri h hw with ⟨_, h'⟩ | ⟨_, h'⟩ <;> exact su_ne h'
  have h2 : ({c, d} : Finset (X → Bool)).card = 2 := Finset.card_pair hcd
  have n3 : b ∉ ({c, d} : Finset (X → Bool)) := by simp [hbc, hbd]
  have h3 : ({b, c, d} : Finset (X → Bool)).card = 3 := by
    have t := Finset.card_insert_of_notMem n3
    omega
  have n4 : a ∉ ({b, c, d} : Finset (X → Bool)) := by simp [hab, hac, had]
  have t := Finset.card_insert_of_notMem n4
  omega

lemma su_chain_sub {X : Type*} [LinearOrder X] [Fintype X] {K : Finset (X → Bool)}
    {a b c d : X → Bool} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K) :
    ({a, b, c, d} : Finset (X → Bool)) ⊆ K := by
  intro v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with h | h | h | h
  · rw [h]; exact ha
  · rw [h]; exact hb
  · rw [h]; exact hc
  · rw [h]; exact hd

lemma suPsi_pos {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2)
    (A : Finset (X → Bool))
    (h : ∃ a b c d : X → Bool, ∃ x y w : X, SuRep A a b c d x y w ∧ SuCol0 χ χ' x y w) :
    suPsi χ χ' A = 0 := by
  unfold suPsi
  rw [if_pos h]

lemma suPsi_neg {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2)
    (A : Finset (X → Bool))
    (h : ¬ ∃ a b c d : X → Bool, ∃ x y w : X, SuRep A a b c d x y w ∧ SuCol0 χ χ' x y w) :
    suPsi χ χ' A = 1 := by
  unfold suPsi
  rw [if_neg h]

lemma suPsi_zero {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2)
    (A : Finset (X → Bool)) (h : suPsi χ χ' A = 0) :
    ∃ a b c d : X → Bool, ∃ x y w : X, SuRep A a b c d x y w ∧ SuCol0 χ χ' x y w := by
  by_contra hne
  have t := suPsi_neg χ χ' A hne
  rw [t] at h
  exact absurd h (by decide)

lemma su_G0 {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2)
    (K : Finset (X → Bool))
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = 4 → suPsi χ χ' A = 0) :
    ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, ∀ d ∈ K, ∀ x y w : X,
      SuStp a b x → SuStp b c y → SuStp c d w → SuCol0 χ χ' x y w := by
  intro a ha b hb c hc d hd x y w hx hy hw
  have h := hm _ (su_chain_sub ha hb hc hd) (su_chain_card hx hy hw)
  obtain ⟨a', b', c', d', x', y', w', ⟨hA, hx', hy', hw'⟩, hcol⟩ := suPsi_zero χ χ' _ h
  obtain ⟨e1, e2, e3, e4⟩ := su_chain4_unique (α := X → Bool) suVlt su_vlt_asymm su_vlt_trans
    a b c d a' b' c' d' ⟨x, hx⟩ ⟨y, hy⟩ ⟨w, hw⟩ ⟨x', hx'⟩ ⟨y', hy'⟩ ⟨w', hw'⟩ hA
  rw [← e1, ← e2] at hx'
  rw [← e2, ← e3] at hy'
  rw [← e3, ← e4] at hw'
  rw [su_unique hx hx', su_unique hy hy', su_unique hw hw']
  exact hcol

lemma su_G1 {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2)
    (K : Finset (X → Bool))
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = 4 → suPsi χ χ' A = 1) :
    ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, ∀ d ∈ K, ∀ x y w : X,
      SuStp a b x → SuStp b c y → SuStp c d w → ¬ SuCol0 χ χ' x y w := by
  intro a ha b hb c hc d hd x y w hx hy hw hcol
  have h1 := hm _ (su_chain_sub ha hb hc hd) (su_chain_card hx hy hw)
  have h0 : suPsi χ χ' ({a, b, c, d} : Finset (X → Bool)) = 0 :=
    suPsi_pos χ χ' _ ⟨a, b, c, d, x, y, w, ⟨rfl, hx, hy, hw⟩, hcol⟩
  rw [h0] at h1
  exact absurd h1 (by decide)

lemma su_split {X : Type*} [LinearOrder X] [Fintype X] (K : Finset (X → Bool))
    (hK : 2 ≤ K.card) :
    ∃ e : X, (∃ m ∈ K, m e = false) ∧ (∃ m ∈ K, m e = true) ∧
      (∀ p ∈ K, ∀ r ∈ K, p e = false → r e = true → SuStp p r e) ∧
      (∀ p ∈ K, ∀ r ∈ K, p e = r e → ∀ x, SuStp p r x → x < e) := by
  classical
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by omega : 0 < K.card)
  obtain ⟨v, hv'⟩ := Finset.card_pos.mp
    (by rw [Finset.card_erase_of_mem hu]; omega : 0 < (K.erase u).card)
  obtain ⟨hvu, hv⟩ := Finset.mem_erase.mp hv'
  obtain ⟨x0, hx0⟩ := Function.ne_iff.mp hvu
  have hne : (Finset.univ.filter (fun x : X => ∃ a ∈ K, ∃ b ∈ K, a x ≠ b x)).Nonempty :=
    ⟨x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, u, hu, hx0⟩⟩
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image _ (fun x : X => x) hne
  obtain ⟨a0, ha0, b0, hb0, hdiff⟩ := (Finset.mem_filter.mp he).2
  have hab : ∀ y, e < y → ∀ a ∈ K, ∀ b ∈ K, a y = b y := by
    intro y hy a ha b hb
    by_contra hc
    have h1 : y ≤ e := hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, b, hb, hc⟩)
    exact absurd hy (not_lt.mpr h1)
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · rcases su_bool_ne _ _ hdiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a0, ha0, h1⟩
    · exact ⟨b0, hb0, h2⟩
  · rcases su_bool_ne _ _ hdiff with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨b0, hb0, h2⟩
    · exact ⟨a0, ha0, h1⟩
  · intro p hp r hr h1 h2
    exact ⟨h1, h2, fun y hy => hab y hy p hp r hr⟩
  · intro p hp r hr hpr x hx
    by_contra hcon
    rcases eq_or_lt_of_le (not_lt.mp hcon) with h | h
    · have t1 := hx.1
      have t2 := hx.2.1
      rw [← h] at t1 t2
      rw [hpr, t2] at t1
      exact absurd t1 (by decide)
    · have t := hab x h p hp r hr
      rw [hx.1, hx.2.1] at t
      exact absurd t (by decide)

lemma su_caterpillar {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool), K.card = n + 2 →
    (∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, ∀ d ∈ K, ∀ x y w : X,
      SuStp a b x → SuStp b c y → SuStp c d w → ¬ (x < y ∧ w < y)) →
    ∃ T T' : Finset X, ∃ q ∈ K, ∃ q' ∈ K, T.card + T'.card = n + 2 ∧
      (∀ x ∈ T, ∃ b ∈ K, SuStp q b x) ∧ (∀ x ∈ T', ∃ a ∈ K, SuStp a q' x) := by
  intro n
  induction n with
  | zero =>
    intro K hK _
    obtain ⟨u, v, huv, hKe⟩ := Finset.card_eq_two.mp (by omega : K.card = 2)
    have hu : u ∈ K := by rw [hKe]; simp
    have hv : v ∈ K := by rw [hKe]; simp
    obtain ⟨x, hx | hx⟩ := su_total huv
    · refine ⟨{x}, {x}, u, hu, v, hv, by simp, ?_, ?_⟩
      · intro x' hx'
        rw [Finset.mem_singleton.mp hx']
        exact ⟨v, hv, hx⟩
      · intro x' hx'
        rw [Finset.mem_singleton.mp hx']
        exact ⟨u, hu, hx⟩
    · refine ⟨{x}, {x}, v, hv, u, hu, by simp, ?_, ?_⟩
      · intro x' hx'
        rw [Finset.mem_singleton.mp hx']
        exact ⟨u, hu, hx⟩
      · intro x' hx'
        rw [Finset.mem_singleton.mp hx']
        exact ⟨v, hv, hx⟩
  | succ n ih =>
    intro K hK NP
    obtain ⟨e, ⟨mF, hmF, hmFe⟩, ⟨mT, hmT, hmTe⟩, hcross, hlow⟩ := su_split K (by omega)
    have key : ∀ p ∈ K, ∀ r ∈ K, ∀ w ∈ K, ∀ z ∈ K, p e = false → r e = false →
        w e = true → z e = true → ∀ x y, SuStp p r x → SuStp w z y → False := by
      intro p hp r hr w hw z hz h1 h2 h3 h4 x y hx hy
      exact NP p hp r hr w hw z hz x e y hx (hcross r hr w hw h2 h3) hy
        ⟨hlow p hp r hr (h1.trans h2.symm) x hx, hlow w hw z hz (h3.trans h4.symm) y hy⟩
    by_cases hone : ∀ p ∈ K, ∀ r ∈ K, p e = true → r e = true → p = r
    · have hK' : (K.erase mT).card = n + 2 := by
        rw [Finset.card_erase_of_mem hmT]; omega
      have hfalse : ∀ p ∈ K.erase mT, p e = false := by
        intro p hp
        obtain ⟨hpne, hpK⟩ := Finset.mem_erase.mp hp
        rcases su_bool_cases (p e) with h | h
        · exact h
        · exact absurd (hone p hpK mT hmT h hmTe) hpne
      obtain ⟨T, T', q, hq, q', hq', hc, hT, hT'⟩ := ih (K.erase mT) hK'
        (fun a ha b hb c hc d hd => NP a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2
          c (Finset.mem_erase.mp hc).2 d (Finset.mem_erase.mp hd).2)
      have hqK : q ∈ K := (Finset.mem_erase.mp hq).2
      have heT : e ∉ T := by
        intro he
        obtain ⟨b, hb, hbe⟩ := hT e he
        have t := hbe.2.1
        rw [hfalse b hb] at t
        exact absurd t (by decide)
      refine ⟨insert e T, T', q, hqK, q', (Finset.mem_erase.mp hq').2, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem heT]; omega
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]
          exact ⟨mT, hmT, hcross q hqK mT hmT (hfalse q hq) hmTe⟩
        · obtain ⟨b, hb, hbx⟩ := hT x h
          exact ⟨b, (Finset.mem_erase.mp hb).2, hbx⟩
      · intro x hx
        obtain ⟨a, ha, hax⟩ := hT' x hx
        exact ⟨a, (Finset.mem_erase.mp ha).2, hax⟩
    · have hone' : ∀ p ∈ K, ∀ r ∈ K, p e = false → r e = false → p = r := by
        intro p hp r hr h1 h2
        by_contra hpr
        apply hone
        intro w hw z hz h3 h4
        by_contra hwz
        obtain ⟨x, hx⟩ := su_total hpr
        obtain ⟨y, hy⟩ := su_total hwz
        rcases hx with hx | hx
        · rcases hy with hy | hy
          · exact key p hp r hr w hw z hz h1 h2 h3 h4 x y hx hy
          · exact key p hp r hr z hz w hw h1 h2 h4 h3 x y hx hy
        · rcases hy with hy | hy
          · exact key r hr p hp w hw z hz h2 h1 h3 h4 x y hx hy
          · exact key r hr p hp z hz w hw h2 h1 h4 h3 x y hx hy
      have hK' : (K.erase mF).card = n + 2 := by
        rw [Finset.card_erase_of_mem hmF]; omega
      have htrue : ∀ p ∈ K.erase mF, p e = true := by
        intro p hp
        obtain ⟨hpne, hpK⟩ := Finset.mem_erase.mp hp
        rcases su_bool_cases (p e) with h | h
        · exact absurd (hone' p hpK mF hmF h hmFe) hpne
        · exact h
      obtain ⟨T, T', q, hq, q', hq', hc, hT, hT'⟩ := ih (K.erase mF) hK'
        (fun a ha b hb c hc d hd => NP a (Finset.mem_erase.mp ha).2 b (Finset.mem_erase.mp hb).2
          c (Finset.mem_erase.mp hc).2 d (Finset.mem_erase.mp hd).2)
      have hq'K : q' ∈ K := (Finset.mem_erase.mp hq').2
      have heT' : e ∉ T' := by
        intro he
        obtain ⟨a, ha, hae⟩ := hT' e he
        have t := hae.1
        rw [htrue a ha] at t
        exact absurd t (by decide)
      refine ⟨T, insert e T', q, (Finset.mem_erase.mp hq).2, q', hq'K, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem heT']; omega
      · intro x hx
        obtain ⟨b, hb, hbx⟩ := hT x hx
        exact ⟨b, (Finset.mem_erase.mp hb).2, hbx⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]
          exact ⟨mF, hmF, hcross mF hmF q' hq'K hmFe (htrue q' hq')⟩
        · obtain ⟨a, ha, hax⟩ := hT' x h
          exact ⟨a, (Finset.mem_erase.mp ha).2, hax⟩

lemma su_side_up {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2) (s : ℕ)
    (hχ : Solon.NoMono χ 3 s 0) (K0 : Finset (X → Bool)) (z : X → Bool) (e : X)
    (hz : ∀ v ∈ K0, SuStp v z e)
    (hlow : ∀ u ∈ K0, ∀ v ∈ K0, ∀ x, SuStp u v x → x < e)
    (hne : K0.Nonempty)
    (G : ∀ a ∈ insert z K0, ∀ b ∈ insert z K0, ∀ c ∈ insert z K0, ∀ d ∈ insert z K0,
      ∀ x y w : X, SuStp a b x → SuStp b c y → SuStp c d w → SuCol0 χ χ' x y w) :
    K0.card < s := by
  have hzn : z ∉ K0 := fun h => su_irrefl (hz z h)
  have hLc : (insert z K0).card = K0.card + 1 := Finset.card_insert_of_notMem hzn
  have hpos : 0 < K0.card := Finset.card_pos.mpr hne
  have hbelow : ∀ u ∈ insert z K0, ∀ v ∈ insert z K0, ∀ x, SuStp u v x → u ∈ K0 := by
    intro u hu v hv x hx
    rcases Finset.mem_insert.mp hu with h | h
    · exfalso
      rw [h] at hx
      rcases Finset.mem_insert.mp hv with h' | h'
      · rw [h'] at hx
        exact su_irrefl hx
      · exact su_asymm hx (hz v h')
    · exact h
  have UP : ∀ u ∈ insert z K0, ∀ v ∈ insert z K0, ∀ w ∈ insert z K0, ∀ x y,
      SuStp u v x → SuStp v w y → x < y := by
    intro u hu v hv w hw x y hx hy
    have hu0 := hbelow u hu v hv x hx
    have hv0 := hbelow v hv w hw y hy
    rcases Finset.mem_insert.mp hw with h | h
    · rw [h] at hy
      rw [su_unique hy (hz v hv0)]
      exact hlow u hu0 v hv0 x hx
    · rcases su_tri hx hy with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · exfalso
        have hye : y < e := hlow v hv0 w h y hy
        rcases G u hu v hv w hw z (Finset.mem_insert_self _ _) x y e hx hy (hz w h) with
          ⟨c1, _⟩ | ⟨c1, _⟩ | ⟨_, c2, _⟩
        · exact absurd (lt_trans c1 h1) (lt_irrefl _)
        · exact absurd (lt_trans c1 h1) (lt_irrefl _)
        · exact absurd (lt_trans c2 hye) (lt_irrefl _)
  have NP : ∀ a ∈ insert z K0, ∀ b ∈ insert z K0, ∀ c ∈ insert z K0, ∀ d ∈ insert z K0,
      ∀ x y w : X, SuStp a b x → SuStp b c y → SuStp c d w → ¬ (x < y ∧ w < y) := by
    intro a ha b hb c hc d hd x y w hx hy hw hp
    exact absurd (lt_trans (UP b hb c hc d hd y w hy hw) hp.2) (lt_irrefl _)
  obtain ⟨T, T', q, hq, q', hq', hc, hT, hT'⟩ :=
    su_caterpillar (K0.card - 1) (insert z K0) (by omega) NP
  have hT1 : T'.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    obtain ⟨a, ha, hax⟩ := hT' x hx
    obtain ⟨c, hc', hcy⟩ := hT' y hy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact absurd (lt_trans h (UP c hc' a ha q' hq' y x (su_real_down hax hcy h) hax))
        (lt_irrefl _)
    · exact absurd (lt_trans h (UP a ha c hc' q' hq' x y (su_real_down hcy hax h) hcy))
        (lt_irrefl _)
  have hbound := su_clique_bound χ 0 s hχ T (by
    intro x hx y hy w hw hxy hyw
    obtain ⟨a, ha, b, hb, c, hc2, d, hd, h1, h2, h3⟩ :=
      su_up_clique (insert z K0) T q hq hT x y w hx hy hw hxy hyw
    rcases G a ha b hb c hc2 d hd x y w h1 h2 h3 with ⟨_, c1⟩ | ⟨_, _, c1⟩ | ⟨c1, _⟩
    · exact absurd (lt_trans hyw c1) (lt_irrefl _)
    · exact c1
    · exact absurd (lt_trans hxy c1) (lt_irrefl _))
  omega

lemma su_side_down {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2) (s : ℕ)
    (hχ : Solon.NoMono χ' 3 s 0) (K1 : Finset (X → Bool)) (z : X → Bool) (e : X)
    (hz : ∀ v ∈ K1, SuStp z v e)
    (hlow : ∀ u ∈ K1, ∀ v ∈ K1, ∀ x, SuStp u v x → x < e)
    (hne : K1.Nonempty)
    (G : ∀ a ∈ insert z K1, ∀ b ∈ insert z K1, ∀ c ∈ insert z K1, ∀ d ∈ insert z K1,
      ∀ x y w : X, SuStp a b x → SuStp b c y → SuStp c d w → SuCol0 χ χ' x y w) :
    K1.card < s := by
  have hzn : z ∉ K1 := fun h => su_irrefl (hz z h)
  have hLc : (insert z K1).card = K1.card + 1 := Finset.card_insert_of_notMem hzn
  have hpos : 0 < K1.card := Finset.card_pos.mpr hne
  have habove : ∀ u ∈ insert z K1, ∀ v ∈ insert z K1, ∀ x, SuStp u v x → v ∈ K1 := by
    intro u hu v hv x hx
    rcases Finset.mem_insert.mp hv with h | h
    · exfalso
      rw [h] at hx
      rcases Finset.mem_insert.mp hu with h' | h'
      · rw [h'] at hx
        exact su_irrefl hx
      · exact su_asymm (hz u h') hx
    · exact h
  have DOWN : ∀ u ∈ insert z K1, ∀ v ∈ insert z K1, ∀ w ∈ insert z K1, ∀ x y,
      SuStp u v x → SuStp v w y → y < x := by
    intro u hu v hv w hw x y hx hy
    have hv1 := habove u hu v hv x hx
    have hw1 := habove v hv w hw y hy
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h] at hx
      rw [su_unique hx (hz v hv1)]
      exact hlow v hv1 w hw1 y hy
    · rcases su_tri hx hy with ⟨h1, _⟩ | ⟨h1, _⟩
      · exfalso
        have hxe : x < e := hlow u h v hv1 x hx
        rcases G z (Finset.mem_insert_self _ _) u hu v hv w hw e x y (hz u h) hx hy with
          ⟨c1, _⟩ | ⟨c1, _⟩ | ⟨_, c2, _⟩
        · exact absurd (lt_trans c1 hxe) (lt_irrefl _)
        · exact absurd (lt_trans c1 hxe) (lt_irrefl _)
        · exact absurd (lt_trans c2 h1) (lt_irrefl _)
      · exact h1
  have NP : ∀ a ∈ insert z K1, ∀ b ∈ insert z K1, ∀ c ∈ insert z K1, ∀ d ∈ insert z K1,
      ∀ x y w : X, SuStp a b x → SuStp b c y → SuStp c d w → ¬ (x < y ∧ w < y) := by
    intro a ha b hb c hc d hd x y w hx hy hw hp
    exact absurd (lt_trans hp.1 (DOWN a ha b hb c hc x y hx hy)) (lt_irrefl _)
  obtain ⟨T, T', q, hq, q', hq', hc, hT, hT'⟩ :=
    su_caterpillar (K1.card - 1) (insert z K1) (by omega) NP
  have hT1 : T.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    obtain ⟨b, hb, hbx⟩ := hT x hx
    obtain ⟨c, hc', hcy⟩ := hT y hy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact absurd (lt_trans h (DOWN q hq b hb c hc' x y hbx (su_real_up hbx hcy h)))
        (lt_irrefl _)
    · exact absurd (lt_trans h (DOWN q hq c hc' b hb y x hcy (su_real_up hcy hbx h)))
        (lt_irrefl _)
  have hbound := su_clique_bound χ' 0 s hχ T' (by
    intro x hx y hy w hw hxy hyw
    obtain ⟨a, ha, b, hb, c, hc2, d, hd, h1, h2, h3⟩ :=
      su_down_clique (insert z K1) T' q' hq' hT' x y w hx hy hw hxy hyw
    rcases G a ha b hb c hc2 d hd w y x h1 h2 h3 with ⟨c1, _⟩ | ⟨c1, _⟩ | ⟨_, _, c1⟩
    · exact absurd (lt_trans hyw c1) (lt_irrefl _)
    · exact absurd (lt_trans hyw c1) (lt_irrefl _)
    · exact c1)
  omega

lemma su_main0 {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2) (s s' : ℕ)
    (K : Finset (X → Bool)) (hs : 2 ≤ s) (hs' : 2 ≤ s') (hK : K.card = s + s' - 1)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = 4 → suPsi χ χ' A = 0)
    (h0 : Solon.NoMono χ 3 s 0) (h0' : Solon.NoMono χ' 3 s' 0) : False := by
  have G := su_G0 χ χ' K hm
  obtain ⟨e, ⟨mF, hmF, hmFe⟩, ⟨mT, hmT, hmTe⟩, hcross, hlow⟩ := su_split K (by omega)
  have hsub0 : ∀ p ∈ insert mT (K.filter (fun p : X → Bool => p e = false)), p ∈ K := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h]; exact hmT
    · exact (Finset.mem_filter.mp h).1
  have hsub1 : ∀ p ∈ insert mF (K.filter (fun p : X → Bool => p e = true)), p ∈ K := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h]; exact hmF
    · exact (Finset.mem_filter.mp h).1
  have hc0 : (K.filter (fun p : X → Bool => p e = false)).card < s :=
    su_side_up χ χ' s h0 (K.filter (fun p : X → Bool => p e = false)) mT e
      (fun p hp => hcross p (Finset.mem_filter.mp hp).1 mT hmT (Finset.mem_filter.mp hp).2 hmTe)
      (fun p hp r hr x hx => hlow p (Finset.mem_filter.mp hp).1 r (Finset.mem_filter.mp hr).1
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm) x hx)
      ⟨mF, Finset.mem_filter.mpr ⟨hmF, hmFe⟩⟩
      (fun a ha b hb c hc d hd => G a (hsub0 a ha) b (hsub0 b hb) c (hsub0 c hc) d (hsub0 d hd))
  have hc1 : (K.filter (fun p : X → Bool => p e = true)).card < s' :=
    su_side_down χ χ' s' h0' (K.filter (fun p : X → Bool => p e = true)) mF e
      (fun p hp => hcross mF hmF p (Finset.mem_filter.mp hp).1 hmFe (Finset.mem_filter.mp hp).2)
      (fun p hp r hr x hx => hlow p (Finset.mem_filter.mp hp).1 r (Finset.mem_filter.mp hr).1
        ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm) x hx)
      ⟨mT, Finset.mem_filter.mpr ⟨hmT, hmTe⟩⟩
      (fun a ha b hb c hc d hd => G a (hsub1 a ha) b (hsub1 b hb) c (hsub1 c hc) d (hsub1 d hd))
  have hsplit : K.card ≤ (K.filter (fun p : X → Bool => p e = false)).card +
      (K.filter (fun p : X → Bool => p e = true)).card := by
    have hsub : K ⊆ K.filter (fun p : X → Bool => p e = false) ∪
        K.filter (fun p : X → Bool => p e = true) := by
      intro p hp
      rcases su_bool_cases (p e) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

lemma su_main1 {X : Type*} [LinearOrder X] [Fintype X] (χ χ' : Finset X → Fin 2) (t t' : ℕ)
    (K : Finset (X → Bool)) (ht : 2 ≤ t) (ht' : 2 ≤ t') (hK : K.card = t + t' - 1)
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = 4 → suPsi χ χ' A = 1)
    (h1 : Solon.NoMono χ 3 t 1) (h1' : Solon.NoMono χ' 3 t' 1) : False := by
  have G := su_G1 χ χ' K hm
  have NP : ∀ a ∈ K, ∀ b ∈ K, ∀ c ∈ K, ∀ d ∈ K, ∀ x y w : X,
      SuStp a b x → SuStp b c y → SuStp c d w → ¬ (x < y ∧ w < y) := by
    intro a ha b hb c hc d hd x y w hx hy hw hp
    exact G a ha b hb c hc d hd x y w hx hy hw (Or.inl hp)
  obtain ⟨T, T', q, hq, q', hq', hc, hT, hT'⟩ := su_caterpillar (K.card - 2) K (by omega) NP
  have hb1 := su_clique_bound χ 1 t h1 T (by
    intro x hx y hy w hw hxy hyw
    obtain ⟨a, ha, b, hb, c, hc2, d, hd, e1, e2, e3⟩ :=
      su_up_clique K T q hq hT x y w hx hy hw hxy hyw
    rcases su_fin2_cases (χ {x, y, w}) with h | h
    · exact False.elim (G a ha b hb c hc2 d hd x y w e1 e2 e3 (Or.inr (Or.inl ⟨hxy, hyw, h⟩)))
    · exact h)
  have hb2 := su_clique_bound χ' 1 t' h1' T' (by
    intro x hx y hy w hw hxy hyw
    obtain ⟨a, ha, b, hb, c, hc2, d, hd, e1, e2, e3⟩ :=
      su_down_clique K T' q' hq' hT' x y w hx hy hw hxy hyw
    rcases su_fin2_cases (χ' {x, y, w}) with h | h
    · exact False.elim (G a ha b hb c hc2 d hd w y x e1 e2 e3 (Or.inr (Or.inr ⟨hyw, hxy, h⟩)))
    · exact h)
  omega

theorem stepping_up_two_colourings : ∀ {X : Type*} [LinearOrder X] [Fintype X] (s s' t t' : ℕ), 2 ≤ s → 2 ≤ s' → 2 ≤ t → 2 ≤ t' → ∀ χ χ' : Finset X → Fin 2, Solon.NoMono χ 3 s 0 → Solon.NoMono χ 3 t 1 → Solon.NoMono χ' 3 s' 0 → Solon.NoMono χ' 3 t' 1 → ∃ ψ : Finset (X → Bool) → Fin 2, Solon.NoMono ψ 4 (s + s' - 1) 0 ∧ Solon.NoMono ψ 4 (t + t' - 1) 1 := by
  intro X _ _ s s' t t' hs hs' ht ht' χ χ' h0 h1 h0' h1'
  refine ⟨suPsi χ χ', ?_, ?_⟩
  · intro K hK
    by_contra hno
    exact su_main0 χ χ' s s' K hs hs' hK (fun A hA hAc => by
      by_contra hne
      exact hno ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hAc⟩, hne⟩) h0 h0'
  · intro K hK
    by_contra hno
    exact su_main1 χ χ' t t' K ht ht' hK (fun A hA hAc => by
      by_contra hne
      exact hno ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hAc⟩, hne⟩) h1 h1'

