import Proofs.Defs

set_option maxHeartbeats 400000

lemma su_bool_eq : ∀ a b c : Bool, a ≠ b → c ≠ b → a = c := by
  intro a b c
  cases a <;> cases b <;> cases c <;> decide

lemma su_bool_ne : ∀ p q : Bool, p ≠ q →
    (p = true ∧ q = false) ∨ (p = false ∧ q = true) := by
  intro p q
  cases p <;> cases q <;> decide

lemma su_tf : ¬ (true = false) := by decide

lemma ct_bool_f : ∀ b : Bool, ¬ b = true → b = false := by decide

lemma su_extend {α : Type*} [DecidableEq α] (S K : Finset α) (n : ℕ)
    (hSK : S ⊆ K) (h1 : S.card ≤ n) (h2 : n ≤ K.card) :
    ∃ A, S ⊆ A ∧ A ⊆ K ∧ A.card = n := by
  have e := Finset.card_sdiff_add_card_eq_card hSK
  obtain ⟨R, hR, hRc⟩ :=
    Finset.exists_subset_card_eq (show n - S.card ≤ (K \ S).card by omega)
  have hd : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp (hR hb)).2 ha
  refine ⟨S ∪ R, fun a ha => Finset.mem_union_left _ ha,
    Finset.union_subset hSK (fun a ha => (Finset.mem_sdiff.mp (hR ha)).1), ?_⟩
  rw [Finset.card_union_of_disjoint hd]
  omega

lemma su_two_pts {α : Type*} [DecidableEq α] (K : Finset α) (h : 2 ≤ K.card) :
    ∃ u ∈ K, ∃ v ∈ K, u ≠ v := by
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq h
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hTc
  exact ⟨u, hT (Finset.mem_insert_self u {v}), v,
    hT (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)), huv⟩

lemma su_uniq {X : Type*} [LinearOrder X] (u v : X → Bool) (x x' : X)
    (h1 : u x ≠ v x) (h2 : ∀ y, x < y → u y = v y)
    (h3 : u x' ≠ v x') (h4 : ∀ y, x' < y → u y = v y) : x' = x := by
  rcases lt_trichotomy x x' with h | h | h
  · exact absurd (h2 x' h) h3
  · exact h.symm
  · exact absurd (h4 x h) h1

lemma ct_split_aux {V : Type*} (K : Finset V) (p : V → Prop) :
    ∃ K1 K0 : Finset V, K1.card + K0.card = K.card ∧
      (∀ a, a ∈ K1 ↔ a ∈ K ∧ p a) ∧ (∀ a, a ∈ K0 ↔ a ∈ K ∧ ¬ p a) := by
  classical
  refine ⟨K.filter p, K.filter (fun a => ¬ p a), ?_,
    fun a => Finset.mem_filter, fun a => Finset.mem_filter⟩
  have hd : Disjoint (K.filter p) (K.filter (fun a => ¬ p a)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
  have hu : K.filter p ∪ K.filter (fun a => ¬ p a) = K := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hv : p v
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hv⟩
  rw [← Finset.card_union_of_disjoint hd, hu]

open Classical

def CtCat {X : Type*} [LinearOrder X] (A : Finset (X → Bool)) : Prop :=
  ∀ x : X, ∀ p ∈ A, ∀ p' ∈ A, ∀ q ∈ A, ∀ q' ∈ A, p ≠ p' → q ≠ q' →
    (∀ y, x < y → p y = q y ∧ p' y = q y ∧ q' y = q y) →
    p x = true → p' x = true → q x = false → q' x = false → False

noncomputable def suDelta {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Finset X :=
  Finset.univ.filter (fun x => ∃ u ∈ A, ∃ v ∈ A, u x ≠ v x ∧ ∀ y, x < y → u y = v y)

noncomputable def ctCol {X Cl : Type*} [LinearOrder X] [Fintype X]
    (a : Cl) (χ : Finset X → Cl) (A : Finset (X → Bool)) : Cl :=
  if CtCat A then χ (suDelta A) else a

lemma ctCol_cat {X Cl : Type*} [LinearOrder X] [Fintype X]
    (a : Cl) (χ : Finset X → Cl) (A : Finset (X → Bool)) (h : CtCat A) :
    ctCol a χ A = χ (suDelta A) := by
  unfold ctCol
  rw [if_pos h]

lemma ctCol_not {X Cl : Type*} [LinearOrder X] [Fintype X]
    (a : Cl) (χ : Finset X → Cl) (A : Finset (X → Bool)) (h : ¬ CtCat A) :
    ctCol a χ A = a := by
  unfold ctCol
  rw [if_neg h]

lemma su_mem_delta {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) (x : X) :
    x ∈ suDelta A ↔ ∃ u ∈ A, ∃ v ∈ A, u x ≠ v x ∧ ∀ y, x < y → u y = v y := by
  unfold suDelta
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ x, h⟩⟩

lemma su_delta_mono {X : Type*} [LinearOrder X] [Fintype X]
    {A B : Finset (X → Bool)} (hAB : A ⊆ B) : suDelta A ⊆ suDelta B := by
  intro x hx
  rw [su_mem_delta] at hx
  obtain ⟨u, hu, v, hv, h⟩ := hx
  exact (su_mem_delta B x).mpr ⟨u, hAB hu, v, hAB hv, h⟩

lemma su_delta_singleton {X : Type*} [LinearOrder X] [Fintype X] (a : X → Bool) :
    suDelta ({a} : Finset (X → Bool)) = ∅ := by
  apply Finset.subset_empty.mp
  intro x hx
  rw [su_mem_delta] at hx
  obtain ⟨u, hu, v, hv, hne, _⟩ := hx
  exact absurd (by rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]) hne

lemma su_delta_ins_sub {X : Type*} [LinearOrder X] [Fintype X] (z : X → Bool)
    (A' : Finset (X → Bool)) (x : X)
    (hA : ∀ w ∈ A', w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    suDelta (insert z A') ⊆ insert x (suDelta A') := by
  intro y hy
  rw [su_mem_delta] at hy
  obtain ⟨u, hu, v, hv, hne, hag⟩ := hy
  rcases Finset.mem_insert.mp hu with hu' | hu'
  · rcases Finset.mem_insert.mp hv with hv' | hv'
    · exact absurd (by rw [hu', hv']) hne
    · have h1 := hA v hv'
      have hyx : y = x := su_uniq v z x y h1.1 h1.2
        (by rw [← hu']; exact fun h => hne h.symm)
        (by intro y' hy'; rw [← hu']; exact (hag y' hy').symm)
      rw [hyx]
      exact Finset.mem_insert_self x _
  · rcases Finset.mem_insert.mp hv with hv' | hv'
    · have h1 := hA u hu'
      have hyx : y = x := su_uniq u z x y h1.1 h1.2
        (by rw [← hv']; exact hne)
        (by intro y' hy'; rw [← hv']; exact hag y' hy')
      rw [hyx]
      exact Finset.mem_insert_self x _
    · exact Finset.mem_insert_of_mem
        ((su_mem_delta A' y).mpr ⟨u, hu', v, hv', hne, hag⟩)

lemma su_delta_ins_sup {X : Type*} [LinearOrder X] [Fintype X] (z : X → Bool)
    (A' : Finset (X → Bool)) (x : X)
    (hA : ∀ w ∈ A', w x ≠ z x ∧ ∀ y, x < y → w y = z y) (hne : A'.Nonempty) :
    insert x (suDelta A') ⊆ suDelta (insert z A') := by
  intro y hy
  rcases Finset.mem_insert.mp hy with hy' | hy'
  · obtain ⟨a, ha⟩ := hne
    rw [hy']
    exact (su_mem_delta (insert z A') x).mpr
      ⟨a, Finset.mem_insert_of_mem ha, z, Finset.mem_insert_self z A',
        (hA a ha).1, (hA a ha).2⟩
  · exact su_delta_mono (Finset.subset_insert z A') hy'

lemma su_delta_notin {X : Type*} [LinearOrder X] [Fintype X] (z : X → Bool)
    (A' : Finset (X → Bool)) (x : X)
    (hA : ∀ w ∈ A', w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    x ∉ suDelta A' := by
  intro hx
  rw [su_mem_delta] at hx
  obtain ⟨u, hu, v, hv, hne, _⟩ := hx
  exact hne (su_bool_eq (u x) (z x) (v x) (hA u hu).1 (hA v hv).1)

lemma su_delta_ins_eq {X : Type*} [LinearOrder X] [Fintype X] (z : X → Bool)
    (A' : Finset (X → Bool)) (x : X)
    (hA : ∀ w ∈ A', w x ≠ z x ∧ ∀ y, x < y → w y = z y) (hne : A'.Nonempty) :
    suDelta (insert z A') = insert x (suDelta A') :=
  Finset.Subset.antisymm (su_delta_ins_sub z A' x hA) (su_delta_ins_sup z A' x hA hne)

lemma su_top {X : Type*} [LinearOrder X] [Fintype X] (K : Finset (X → Bool))
    (u v : X → Bool) (hu : u ∈ K) (hv : v ∈ K) (hne : u ≠ v) :
    ∃ x : X, (∀ a ∈ K, ∀ a' ∈ K, ∀ y, x < y → a y = a' y) ∧
      ∃ a ∈ K, ∃ a' ∈ K, a x ≠ a' x := by
  obtain ⟨S, hSdef⟩ : ∃ S : Finset X,
      S = Finset.univ.filter (fun x : X => ∃ a ∈ K, ∃ a' ∈ K, a x ≠ a' x) := ⟨_, rfl⟩
  have hmem : ∀ y : X, y ∈ S ↔ ∃ a ∈ K, ∃ a' ∈ K, a y ≠ a' y := by
    intro y
    rw [hSdef, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ y, h⟩⟩
  have hS : S.Nonempty := by
    by_contra hemp
    apply hne
    funext x
    by_contra hx
    exact hemp ⟨x, (hmem x).mpr ⟨u, hu, v, hv, hx⟩⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image S (fun x : X => x) hS
  refine ⟨x, ?_, (hmem x).mp hx⟩
  intro a ha a' ha' y hxy
  by_contra hab
  have hy : y ∈ S := (hmem y).mpr ⟨a, ha, a', ha', hab⟩
  exact absurd (hmax y hy) (not_le.mpr hxy)

lemma su_tf_pts {X : Type*} [LinearOrder X] [Fintype X] (K : Finset (X → Bool)) (x : X)
    (a a' : X → Bool) (ha : a ∈ K) (ha' : a' ∈ K) (hne : a x ≠ a' x) :
    ∃ p ∈ K, p x = true ∧ ∃ q ∈ K, q x = false := by
  rcases su_bool_ne (a x) (a' x) hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨a, ha, h1, a', ha', h2⟩
  · exact ⟨a', ha', h2, a, ha, h1⟩

lemma ct_sub {X : Type*} [LinearOrder X] {A C : Finset (X → Bool)} (h : A ⊆ C)
    (hc : CtCat C) : CtCat A := by
  intro x p hp p' hp' q hq q' hq'
  exact hc x p (h hp) p' (h hp') q (h hq) q' (h hq')

lemma ct_single {X : Type*} [LinearOrder X] (w : X → Bool) :
    CtCat ({w} : Finset (X → Bool)) := by
  intro x p hp p' hp' q hq q' hq' hpp hqq hag hpt hp't hqf hq'f
  exact hpp ((Finset.mem_singleton.mp hp).trans (Finset.mem_singleton.mp hp').symm)

lemma ct_peel {X : Type*} [LinearOrder X] [Fintype X] (C : Finset (X → Bool))
    (hc : CtCat C) (u v : X → Bool) (hu : u ∈ C) (hv : v ∈ C) (hne : u ≠ v) :
    ∃ x : X, ∃ z ∈ C,
      (∀ w ∈ C.erase z, w x ≠ z x ∧ ∀ y, x < y → w y = z y) ∧ (C.erase z).Nonempty := by
  obtain ⟨x, hag, a, ha, a', ha', hne'⟩ := su_top C u v hu hv hne
  obtain ⟨p, hp, hpt, q, hq, hqf⟩ := su_tf_pts C x a a' ha ha' hne'
  have hpq : p ≠ q := fun e => su_tf (hpt.symm.trans (by rw [e]; exact hqf))
  by_cases h1 : ∃ p2 ∈ C, p2 ≠ p ∧ p2 x = true
  · by_cases h2 : ∃ q2 ∈ C, q2 ≠ q ∧ q2 x = false
    · exfalso
      obtain ⟨p2, hp2, hp2p, hp2t⟩ := h1
      obtain ⟨q2, hq2, hq2q, hq2f⟩ := h2
      exact hc x p hp p2 hp2 q hq q2 hq2 (fun e => hp2p e.symm) (fun e => hq2q e.symm)
        (fun y hy => ⟨hag p hp q hq y hy, hag p2 hp2 q hq y hy, hag q2 hq2 q hq y hy⟩)
        hpt hp2t hqf hq2f
    · refine ⟨x, q, hq, ?_, ⟨p, Finset.mem_erase.mpr ⟨hpq, hp⟩⟩⟩
      intro w hw
      obtain ⟨hwq, hwC⟩ := Finset.mem_erase.mp hw
      refine ⟨?_, fun y hy => hag w hwC q hq y hy⟩
      intro hwx
      exact h2 ⟨w, hwC, hwq, hwx.trans hqf⟩
  · refine ⟨x, p, hp, ?_, ⟨q, Finset.mem_erase.mpr ⟨hpq.symm, hq⟩⟩⟩
    intro w hw
    obtain ⟨hwp, hwC⟩ := Finset.mem_erase.mp hw
    refine ⟨?_, fun y hy => hag w hwC p hp y hy⟩
    intro hwx
    exact h1 ⟨w, hwC, hwp, hwx.trans hpt⟩

lemma ct_card {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ C : Finset (X → Bool), C.card ≤ n → CtCat C →
      C.card ≤ (suDelta C).card + 1 := by
  intro n
  induction n with
  | zero =>
    intro C hC _
    omega
  | succ n ih =>
    intro C hCn hcat
    by_cases h1 : C.card ≤ 1
    · omega
    · obtain ⟨u, hu, v, hv, huv⟩ := su_two_pts C (by omega)
      obtain ⟨x, z, hz, hrest, hne'⟩ := ct_peel C hcat u v hu hv huv
      have hsup := su_delta_ins_sup z (C.erase z) x hrest hne'
      rw [Finset.insert_erase hz] at hsup
      have hxn := su_delta_notin z (C.erase z) x hrest
      have e1 := Finset.card_erase_of_mem hz
      have e2 := Finset.card_le_card hsup
      rw [Finset.card_insert_of_notMem hxn] at e2
      have e3 := ih (C.erase z) (by omega) (ct_sub (Finset.erase_subset z C) hcat)
      omega

lemma ct_real {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ C : Finset (X → Bool), C.card ≤ n → CtCat C → C.Nonempty →
      ∀ D : Finset X, D ⊆ suDelta C →
        ∃ A : Finset (X → Bool), A ⊆ C ∧ A.card = D.card + 1 ∧ suDelta A = D := by
  intro n
  induction n with
  | zero =>
    intro C hC0 _ hne D _
    exfalso
    obtain ⟨a, ha⟩ := hne
    have := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  | succ n ih =>
    intro C hCn hcomb hne D hD
    by_cases hDe : D = ∅
    · obtain ⟨a, ha⟩ := hne
      refine ⟨({a} : Finset (X → Bool)), Finset.singleton_subset_iff.mpr ha, ?_, ?_⟩
      · have h1 : ({a} : Finset (X → Bool)).card = 1 := Finset.card_singleton a
        have h2 : (∅ : Finset X).card = 0 := Finset.card_empty
        rw [hDe]
        omega
      · rw [hDe]
        exact su_delta_singleton a
    · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hDe
      have hdC := hD hd
      rw [su_mem_delta] at hdC
      obtain ⟨u, hu, v, hv, huv, _⟩ := hdC
      have huv' : u ≠ v := fun h => huv (by rw [h])
      obtain ⟨x, z, hz, hrest, hne'⟩ := ct_peel C hcomb u v hu hv huv'
      have hcard : (C.erase z).card ≤ n := by
        have := Finset.card_erase_of_mem hz
        omega
      have hcomb' : CtCat (C.erase z) := ct_sub (Finset.erase_subset z C) hcomb
      have hsub : suDelta C ⊆ insert x (suDelta (C.erase z)) := by
        have h := su_delta_ins_sub z (C.erase z) x hrest
        rw [Finset.insert_erase hz] at h
        exact h
      by_cases hxD : x ∈ D
      · have hD' : D.erase x ⊆ suDelta (C.erase z) := by
          intro y hy
          obtain ⟨hyx, hyD⟩ := Finset.mem_erase.mp hy
          rcases Finset.mem_insert.mp (hsub (hD hyD)) with h | h
          · exact absurd h hyx
          · exact h
        obtain ⟨A', hA'sub, hA'card, hA'd⟩ :=
          ih (C.erase z) hcard hcomb' hne' (D.erase x) hD'
        have hzA : z ∉ A' := fun h => (Finset.mem_erase.mp (hA'sub h)).1 rfl
        have hA'ne : A'.Nonempty := Finset.card_pos.mp (by omega)
        refine ⟨insert z A', ?_, ?_, ?_⟩
        · exact Finset.insert_subset hz (hA'sub.trans (Finset.erase_subset z C))
        · rw [Finset.card_insert_of_notMem hzA, hA'card]
          have h1 := Finset.card_erase_of_mem hxD
          have hpos : 0 < D.card := Finset.card_pos.mpr ⟨x, hxD⟩
          omega
        · rw [su_delta_ins_eq z A' x (fun w hw => hrest w (hA'sub hw)) hA'ne, hA'd]
          exact Finset.insert_erase hxD
      · have hD' : D ⊆ suDelta (C.erase z) := by
          intro y hy
          rcases Finset.mem_insert.mp (hsub (hD hy)) with h | h
          · exact absurd (by rw [← h]; exact hy) hxD
          · exact h
        obtain ⟨A', h1, h2, h3⟩ := ih (C.erase z) hcard hcomb' hne' D hD'
        exact ⟨A', h1.trans (Finset.erase_subset z C), h2, h3⟩

lemma ct_ins {X : Type*} [LinearOrder X] [Fintype X] (z : X → Bool)
    (C' : Finset (X → Bool)) (x : X)
    (hrest : ∀ w ∈ C', w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hc : CtCat C') : CtCat (insert z C') := by
  have key1 : ∀ u ∈ insert z C', ∀ w ∈ insert z C', u x = w x → u ≠ w →
      u ∈ C' ∧ w ∈ C' := by
    intro u hu w hw he hne
    rcases Finset.mem_insert.mp hu with hu' | hu'
    · rcases Finset.mem_insert.mp hw with hw' | hw'
      · exact absurd (hu'.trans hw'.symm) hne
      · exact ((hrest w hw').1 (by rw [← he, hu'])).elim
    · rcases Finset.mem_insert.mp hw with hw' | hw'
      · exact ((hrest u hu').1 (by rw [he, hw'])).elim
      · exact ⟨hu', hw'⟩
  have above : ∀ u ∈ insert z C', ∀ y, x < y → u y = z y := by
    intro u hu y hy
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h]
    · exact (hrest u h).2 y hy
  intro y p hp p' hp' q hq q' hq' hpp hqq hag hpt hp't hqf hq'f
  have hpq : p ≠ q := fun e => su_tf (hpt.symm.trans (by rw [e]; exact hqf))
  have hp'q : p' ≠ q := fun e => su_tf (hp't.symm.trans (by rw [e]; exact hqf))
  have hpq' : p ≠ q' := fun e => su_tf (hpt.symm.trans (by rw [e]; exact hq'f))
  rcases lt_trichotomy x y with h | h | h
  · have e1 := above p hp y h
    have e2 := above q hq y h
    rw [hpt] at e1
    rw [hqf] at e2
    exact su_tf (e1.trans e2.symm)
  · obtain ⟨m1, m2⟩ := key1 p hp p' hp' (by rw [h]; exact hpt.trans hp't.symm) hpp
    obtain ⟨m3, m4⟩ := key1 q hq q' hq' (by rw [h]; exact hqf.trans hq'f.symm) hqq
    exact hc y p m1 p' m2 q m3 q' m4 hpp hqq hag hpt hp't hqf hq'f
  · obtain ⟨g1, g2, g3⟩ := hag x h
    obtain ⟨m1, m3⟩ := key1 p hp q hq g1 hpq
    obtain ⟨m2, _⟩ := key1 p' hp' q hq g2 hp'q
    obtain ⟨m4, _⟩ := key1 q' hq' p hp (g3.trans g1.symm) (fun e => hpq' e.symm)
    exact hc y p m1 p' m2 q m3 q' m4 hpp hqq hag hpt hp't hqf hq'f

lemma ct_grow {X : Type*} [LinearOrder X] [Fintype X] (K C' : Finset (X → Bool))
    (x : X) (z : X → Bool) (hz : z ∈ K) (hC'K : C' ⊆ K)
    (hag : ∀ a ∈ K, ∀ a' ∈ K, ∀ y, x < y → a y = a' y)
    (hne : ∀ w ∈ C', w x ≠ z x) (hc : CtCat C') :
    ∃ C : Finset (X → Bool), C ⊆ K ∧ CtCat C ∧ C.card = C'.card + 1 :=
  ⟨insert z C', Finset.insert_subset hz hC'K,
    ct_ins z C' x (fun w hw => ⟨hne w hw, fun y hy => hag w (hC'K hw) z hz y hy⟩) hc,
    Finset.card_insert_of_notMem (fun h => hne z h rfl)⟩

lemma ct_split {X : Type*} [LinearOrder X] [Fintype X] (K : Finset (X → Bool))
    (h : 2 ≤ K.card) :
    ∃ x : X, ∃ P Q : Finset (X → Bool), P ⊆ K ∧ Q ⊆ K ∧ P.Nonempty ∧ Q.Nonempty ∧
      P.card + Q.card = K.card ∧ (∀ w ∈ P, w x = true) ∧ (∀ w ∈ Q, w x = false) ∧
      (∀ a ∈ K, ∀ a' ∈ K, ∀ y, x < y → a y = a' y) := by
  obtain ⟨u, hu, v, hv, huv⟩ := su_two_pts K h
  obtain ⟨x, hag, a, ha, a', ha', hne⟩ := su_top K u v hu hv huv
  obtain ⟨p, hp, hpt, q, hq, hqf⟩ := su_tf_pts K x a a' ha ha' hne
  obtain ⟨P, Q, hsum, hPm, hQm⟩ := ct_split_aux K (fun w => w x = true)
  exact ⟨x, P, Q, fun w hw => ((hPm w).mp hw).1, fun w hw => ((hQm w).mp hw).1,
    ⟨p, (hPm p).mpr ⟨hp, hpt⟩⟩,
    ⟨q, (hQm q).mpr ⟨hq, fun h => su_tf (h.symm.trans hqf)⟩⟩, hsum,
    fun w hw => ((hPm w).mp hw).2, fun w hw => ct_bool_f _ ((hQm w).mp hw).2, hag⟩

lemma ct_extract {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ m : ℕ, ∀ K : Finset (X → Bool), 2 ^ m < K.card →
      ∃ C : Finset (X → Bool), C ⊆ K ∧ CtCat C ∧ C.card = m + 2 := by
  intro m
  induction m with
  | zero =>
    intro K hK
    rw [pow_zero] at hK
    obtain ⟨x, P, Q, hP, hQ, hPn, hQn, hsum, hPt, hQf, hag⟩ := ct_split K (by omega)
    obtain ⟨w, hw⟩ := hPn
    obtain ⟨z, hz⟩ := hQn
    obtain ⟨C, hCK, hC, hCc⟩ := ct_grow K {w} x z (hQ hz)
      (Finset.singleton_subset_iff.mpr (hP hw)) hag
      (by
        intro w' hw' h
        rw [Finset.mem_singleton.mp hw', hPt w hw, hQf z hz] at h
        exact su_tf h)
      (ct_single w)
    have h1 := Finset.card_singleton w
    exact ⟨C, hCK, hC, by omega⟩
  | succ m ih =>
    intro K hK
    have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have h0 := pow_pos (show (0 : ℕ) < 2 by norm_num) m
    obtain ⟨x, P, Q, hP, hQ, hPn, hQn, hsum, hPt, hQf, hag⟩ := ct_split K (by omega)
    by_cases hPbig : 2 ^ m < P.card
    · obtain ⟨C', hC'P, hC', hC'c⟩ := ih P hPbig
      obtain ⟨z, hz⟩ := hQn
      obtain ⟨C, hCK, hC, hCc⟩ := ct_grow K C' x z (hQ hz) (hC'P.trans hP) hag
        (by
          intro w hw h
          rw [hPt w (hC'P hw), hQf z hz] at h
          exact su_tf h)
        hC'
      exact ⟨C, hCK, hC, by omega⟩
    · have hQbig : 2 ^ m < Q.card := by omega
      obtain ⟨C', hC'Q, hC', hC'c⟩ := ih Q hQbig
      obtain ⟨z, hz⟩ := hPn
      obtain ⟨C, hCK, hC, hCc⟩ := ct_grow K C' x z (hP hz) (hC'Q.trans hQ) hag
        (by
          intro w hw h
          rw [hQf w (hC'Q hw), hPt z hz] at h
          exact su_tf h.symm)
        hC'
      exact ⟨C, hCK, hC, by omega⟩

lemma ct_bound {X Cl : Type*} [LinearOrder X] [Fintype X] (k t : ℕ) (a : Cl)
    (χ : Finset X → Cl) (i : Cl) (hχ : Solon.NoMono χ k t i)
    (K : Finset (X → Bool))
    (hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 → ctCol a χ A = i)
    (Cc : Finset (X → Bool)) (hC : Cc ⊆ K) (hcat : CtCat Cc) :
    Cc.card ≤ t := by
  by_contra hbig
  have hcard := ct_card Cc.card Cc (le_refl _) hcat
  obtain ⟨S, hS, hSc⟩ :=
    Finset.exists_subset_card_eq (show t ≤ (suDelta Cc).card by omega)
  obtain ⟨D, hD, hDne⟩ := hχ S hSc
  obtain ⟨hDS, hDc⟩ := Finset.mem_powersetCard.mp hD
  have hCne : Cc.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hAC, hAcard, hAd⟩ :=
    ct_real Cc.card Cc (le_refl _) hcat hCne D (hDS.trans hS)
  have hcol := hm A (hAC.trans hC) (by rw [hAcard, hDc])
  rw [ctCol_cat a χ A (ct_sub hAC hcat), hAd] at hcol
  exact hDne hcol

lemma ct_other {X Cl : Type*} [LinearOrder X] [Fintype X] (k : ℕ) (hk : 3 ≤ k)
    (a : Cl) (χ : Finset X → Cl) (i : Cl) (hia : i ≠ a) (t : ℕ) (hkt : k ≤ t)
    (hχ : Solon.NoMono χ k t i) :
    Solon.NoMono (ctCol a χ) (k + 1) (t + 1) i := by
  intro K hK
  by_contra hno
  have hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 → ctCol a χ A = i := by
    intro A hA hc
    by_contra hne
    exact hno ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hc⟩, hne⟩
  have hcat : CtCat K := by
    intro x p hp p' hp' q hq q' hq' hpp hqq hag hpt hp't hqf hq'f
    have hS4 : ({p, p', q, q'} : Finset (X → Bool)).card ≤ k + 1 := by
      have h1 := Finset.card_insert_le p ({p', q, q'} : Finset (X → Bool))
      have h2 := Finset.card_insert_le p' ({q, q'} : Finset (X → Bool))
      have h3 := Finset.card_insert_le q ({q'} : Finset (X → Bool))
      rw [Finset.card_singleton] at h3
      omega
    have hS4K : ({p, p', q, q'} : Finset (X → Bool)) ⊆ K := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h | h | h
      · rw [h]
        exact hp
      · rw [h]
        exact hp'
      · rw [h]
        exact hq
      · rw [h]
        exact hq'
    obtain ⟨A, hSA, hAK, hAc⟩ :=
      su_extend ({p, p', q, q'} : Finset (X → Bool)) K (k + 1) hS4K hS4 (by omega)
    have hnot : ¬ CtCat A := fun hA => hA x p
      (hSA (Finset.mem_insert_self p _)) p'
      (hSA (Finset.mem_insert_of_mem (Finset.mem_insert_self p' _))) q
      (hSA (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_self q _)))) q'
      (hSA (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self q')))))
      hpp hqq hag hpt hp't hqf hq'f
    have h1 := hm A hAK hAc
    rw [ctCol_not a χ A hnot] at h1
    exact hia h1.symm
  have hb := ct_bound k t a χ i hχ K hm K (Finset.Subset.refl K) hcat
  omega

lemma ct_main_a {X Cl : Type*} [LinearOrder X] [Fintype X] (k : ℕ) (a : Cl)
    (χ : Finset X → Cl) (s : ℕ) (ha : Solon.NoMono χ k s a) (n : ℕ)
    (hn : 2 ^ (s - 1) < n) :
    Solon.NoMono (ctCol a χ) (k + 1) n a := by
  intro K hK
  by_contra hno
  have hm : ∀ A : Finset (X → Bool), A ⊆ K → A.card = k + 1 → ctCol a χ A = a := by
    intro A hA hc
    by_contra hne
    exact hno ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hc⟩, hne⟩
  obtain ⟨Cc, hCK, hcat, hCc⟩ := ct_extract (s - 1) K (by rw [hK]; exact hn)
  have hb := ct_bound k s a χ a ha K hm Cc hCK hcat
  omega

theorem caterpillar_palette_all_uniformities : ∀ {X C : Type*} [LinearOrder X] [Fintype X] (k : ℕ) (a : C) (s : C → ℕ), 3 ≤ k → (∀ i, i ≠ a → k ≤ s i) → ∀ χ : Finset X → C, (∀ i, Solon.NoMono χ k (s i) i) → ∃ ψ : Finset (X → Bool) → C, (∀ i, i ≠ a → Solon.NoMono ψ (k + 1) (s i + 1) i) ∧ ∀ n : ℕ, 2 ^ (s a - 1) < n → Solon.NoMono ψ (k + 1) n a := by
  intro X C _ _ k a s hk hs χ hχ
  exact ⟨ctCol a χ, fun i hi => ct_other k hk a χ i hi (s i) (hs i hi) (hχ i),
    fun n hn => ct_main_a k a χ (s a) (hχ a) n hn⟩

