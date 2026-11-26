import Proofs.Defs

set_option maxHeartbeats 0
set_option maxRecDepth 4096

open Classical

namespace NearCatFive

lemma bool_eq : ∀ a b c : Bool, a ≠ b → c ≠ b → a = c := by
  intro a b c
  cases a <;> cases b <;> cases c <;> decide

lemma bool_sides : ∀ a b : Bool, a ≠ b →
    (a = false ∧ b = true) ∨ (a = true ∧ b = false) := by
  intro a b
  cases a <;> cases b <;> decide

lemma level_unique {X : Type*} [LinearOrder X]
    (u v : X → Bool) (x y : X)
    (hx : u x ≠ v x)
    (hax : ∀ z, x < z → u z = v z)
    (hy : u y ≠ v y)
    (hay : ∀ z, y < z → u z = v z) : y = x := by
  rcases lt_trichotomy x y with h | h | h
  · exact (hy (hax y h)).elim
  · exact h.symm
  · exact (hx (hay x h)).elim

lemma extend {V : Type*} [DecidableEq V]
    (S K : Finset V) (n : ℕ)
    (hSK : S ⊆ K) (hSn : S.card ≤ n) (hnK : n ≤ K.card) :
    ∃ A, S ⊆ A ∧ A ⊆ K ∧ A.card = n := by
  have he := Finset.card_sdiff_add_card_eq_card hSK
  obtain ⟨R, hR, hRc⟩ :=
    Finset.exists_subset_card_eq
      (show n - S.card ≤ (K \ S).card by omega)
  have hd : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (Finset.mem_sdiff.mp (hR hy)).2 hx
  refine ⟨S ∪ R, Finset.subset_union_left,
    Finset.union_subset hSK
      (fun x hx => (Finset.mem_sdiff.mp (hR hx)).1), ?_⟩
  rw [Finset.card_union_of_disjoint hd]
  omega

lemma two_points {V : Type*} [DecidableEq V]
    (K : Finset V) (hK : 2 ≤ K.card) :
    ∃ u ∈ K, ∃ v ∈ K, u ≠ v := by
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hK
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hAc
  exact ⟨u, hA (by simp), v, hA (by simp), huv⟩

def Above {X : Type*} [LinearOrder X]
    (K : Finset (X → Bool)) (x : X) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ∀ y, x < y → u y = v y

def side {X : Type*}
    (K : Finset (X → Bool)) (x : X) (d : Bool) :
    Finset (X → Bool) :=
  K.filter (fun v => v x = d)

def Split {X : Type*} [LinearOrder X]
    (K : Finset (X → Bool)) (x : X) : Prop :=
  Above K x ∧ ∃ u ∈ K, ∃ v ∈ K, u x ≠ v x

def Cat {X : Type*} [LinearOrder X]
    (K : Finset (X → Bool)) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ∀ w ∈ K, ∀ z ∈ K, ∀ x : X,
    u ≠ v → w ≠ z →
    (∀ y, x < y → u y = w y ∧ v y = w y ∧ z y = w y) →
    u x = v x → w x = z x → u x = w x

noncomputable def delta {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) : Finset X :=
  Finset.univ.filter (fun x =>
    ∃ u ∈ K, ∃ v ∈ K,
      u x ≠ v x ∧ ∀ y, x < y → u y = v y)

lemma mem_side {X : Type*}
    (K : Finset (X → Bool)) (x : X) (d : Bool) (v : X → Bool) :
    v ∈ side K x d ↔ v ∈ K ∧ v x = d := by
  exact Finset.mem_filter

lemma side_sub {X : Type*}
    (K : Finset (X → Bool)) (x : X) (d : Bool) :
    side K x d ⊆ K :=
  Finset.filter_subset _ _

lemma side_cards {X : Type*} [Fintype X]
    (K : Finset (X → Bool)) (x : X) :
    (side K x false).card + (side K x true).card = K.card := by
  have hd : Disjoint (side K x false) (side K x true) := by
    rw [Finset.disjoint_left]
    intro v hv hw
    have hf := (mem_side K x false v).mp hv
    have ht := (mem_side K x true v).mp hw
    exact (by decide : (false : Bool) ≠ true) (hf.2.symm.trans ht.2)
  have hu : side K x false ∪ side K x true = K := by
    ext v
    cases h : v x <;> simp [side, h]
  rw [← Finset.card_union_of_disjoint hd, hu]

lemma top {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (hK : 2 ≤ K.card) :
    ∃ x, Split K x := by
  obtain ⟨u, hu, v, hv, huv⟩ := two_points K hK
  let S : Finset X :=
    Finset.univ.filter
      (fun x => ∃ p ∈ K, ∃ q ∈ K, p x ≠ q x)
  have hmem : ∀ x, x ∈ S ↔ ∃ p ∈ K, ∃ q ∈ K, p x ≠ q x := by
    intro x
    simp [S]
  have hS : S.Nonempty := by
    by_contra hn
    apply huv
    funext x
    by_contra hx
    exact hn ⟨x, (hmem x).mpr ⟨u, hu, v, hv, hx⟩⟩
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_max_image S (fun x : X => x) hS
  refine ⟨x, ?_, (hmem x).mp hx⟩
  intro p hp q hq y hxy
  by_contra hne
  have hy : y ∈ S := (hmem y).mpr ⟨p, hp, q, hq, hne⟩
  exact (not_le.mpr hxy) (hmax y hy)

lemma split_points {X : Type*} [LinearOrder X]
    {K : Finset (X → Bool)} {x : X} (hx : Split K x) :
    ∃ p ∈ K, p x = false ∧ ∃ q ∈ K, q x = true := by
  obtain ⟨u, hu, v, hv, hne⟩ := hx.2
  rcases bool_sides (u x) (v x) hne with h | h
  · exact ⟨u, hu, h.1, v, hv, h.2⟩
  · exact ⟨v, hv, h.2, u, hu, h.1⟩

lemma cat_sub {X : Type*} [LinearOrder X]
    {A K : Finset (X → Bool)} (hAK : A ⊆ K) (hK : Cat K) :
    Cat A := by
  intro u hu v hv w hw z hz
  exact hK u (hAK hu) v (hAK hv) w (hAK hw) z (hAK hz)

lemma cat_small {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (hK : K.card ≤ 3) : Cat K := by
  intro u hu v hv w hw z hz x huv hwz hag huvx hwzx
  by_contra hux
  have huw : u ≠ w := fun h =>
    hux (congrArg (fun f : X → Bool => f x) h)
  have huz : u ≠ z := fun h =>
    hux ((congrArg (fun f : X → Bool => f x) h).trans hwzx.symm)
  have hvw : v ≠ w := fun h =>
    hux (huvx.trans (congrArg (fun f : X → Bool => f x) h))
  have hvz : v ≠ z := fun h =>
    hux (huvx.trans
      ((congrArg (fun f : X → Bool => f x) h).trans hwzx.symm))
  have hc : ({u, v, w, z} : Finset (X → Bool)).card = 4 := by
    simp [huv, huw, huz, hvw, hvz, hwz]
  have hs : ({u, v, w, z} : Finset (X → Bool)) ⊆ K := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hh := Finset.card_le_card hs
  omega

lemma pair_away {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (C : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ C, w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (p q r : X → Bool) (y : X)
    (hp : p ∈ insert z C) (hq : q ∈ insert z C)
    (hrm : r ∈ insert z C)
    (hpq : p ≠ q) (he : p y = q y) (hne : p y ≠ r y)
    (hag : ∀ t, y < t → p t = r t ∧ q t = r t) :
    p ≠ z := by
  intro hpz
  have hqC : q ∈ C := by
    rcases Finset.mem_insert.mp hq with h | h
    · exact (hpq (hpz.trans h.symm)).elim
    · exact h
  have hrC : r ∈ C := by
    rcases Finset.mem_insert.mp hrm with h | h
    · exact (hne (by rw [hpz, h])).elim
    · exact h
  have hyx : y = x :=
    level_unique r z x y (hr r hrC).1 (hr r hrC).2
      (fun h => hne (by rw [hpz]; exact h.symm))
      (fun t ht =>
        (hag t ht).1.symm.trans
          (congrArg (fun f : X → Bool => f t) hpz))
  apply (hr q hqC).1
  rw [← hyx, ← hpz]
  exact he.symm

lemma cat_insert {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (C : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ C, w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hc : Cat C) : Cat (insert z C) := by
  intro u hu v hv w hw t ht y huv hwt hag huvx hwtx
  by_contra hne
  have hun : u ≠ z :=
    pair_away z C x hr u v w y hu hv hw huv huvx hne
      (fun r hr' => ⟨(hag r hr').1, (hag r hr').2.1⟩)
  have hvn : v ≠ z :=
    pair_away z C x hr v u w y hv hu hw huv.symm huvx.symm
      (fun h => hne (huvx.trans h))
      (fun r hr' => ⟨(hag r hr').2.1, (hag r hr').1⟩)
  have hwn : w ≠ z :=
    pair_away z C x hr w t u y hw ht hu hwt hwtx
      (fun h => hne h.symm)
      (fun r hr' =>
        ⟨(hag r hr').1.symm,
          (hag r hr').2.2.trans (hag r hr').1.symm⟩)
  have htn : t ≠ z :=
    pair_away z C x hr t w u y ht hw hu hwt.symm hwtx.symm
      (fun h => hne (hwtx.trans h).symm)
      (fun r hr' =>
        ⟨(hag r hr').2.2.trans (hag r hr').1.symm,
          (hag r hr').1.symm⟩)
  exact hne (hc
    u ((Finset.mem_insert.mp hu).resolve_left hun)
    v ((Finset.mem_insert.mp hv).resolve_left hvn)
    w ((Finset.mem_insert.mp hw).resolve_left hwn)
    t ((Finset.mem_insert.mp ht).resolve_left htn)
    y huv hwt hag huvx hwtx)

lemma cat_side_bound {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X)
    (hc : Cat K) (hag : Above K x) :
    (side K x false).card ≤ 1 ∨ (side K x true).card ≤ 1 := by
  by_cases hf : (side K x false).card ≤ 1
  · exact Or.inl hf
  by_cases ht : (side K x true).card ≤ 1
  · exact Or.inr ht
  obtain ⟨p, hp, p', hp', hpp⟩ :=
    two_points (side K x false) (by omega)
  obtain ⟨q, hq, q', hq', hqq⟩ :=
    two_points (side K x true) (by omega)
  have hp0 := (mem_side K x false p).mp hp
  have hp1 := (mem_side K x false p').mp hp'
  have hq0 := (mem_side K x true q).mp hq
  have hq1 := (mem_side K x true q').mp hq'
  have he := hc p hp0.1 p' hp1.1 q hq0.1 q' hq1.1 x hpp hqq
    (fun y hy =>
      ⟨hag p hp0.1 q hq0.1 y hy,
        hag p' hp1.1 q hq0.1 y hy,
        hag q' hq1.1 q hq0.1 y hy⟩)
    (hp0.2.trans hp1.2.symm) (hq0.2.trans hq1.2.symm)
  exact ((by decide : (false : Bool) ≠ true)
    (hp0.2.symm.trans (he.trans hq0.2))).elim

lemma peel {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (hc : Cat K) (hK : 2 ≤ K.card) :
    ∃ x : X, ∃ z ∈ K,
      (∀ w ∈ K.erase z, w x ≠ z x ∧ ∀ y, x < y → w y = z y) ∧
      (K.erase z).Nonempty := by
  obtain ⟨x, hx⟩ := top K hK
  obtain ⟨p, hp, hpf, q, hq, hqt⟩ := split_points hx
  have core (d : Bool) (z o : X → Bool)
      (hz : z ∈ K) (ho : o ∈ K) (hzd : z x = d)
      (hoz : o x ≠ z x) (hs : (side K x d).card ≤ 1) :
      ∃ x : X, ∃ z ∈ K,
        (∀ w ∈ K.erase z,
          w x ≠ z x ∧ ∀ y, x < y → w y = z y) ∧
        (K.erase z).Nonempty := by
    refine ⟨x, z, hz, ?_, ⟨o, Finset.mem_erase.mpr ⟨?_, ho⟩⟩⟩
    · intro w hw
      obtain ⟨hwz, hwK⟩ := Finset.mem_erase.mp hw
      refine ⟨?_, fun y hy => hx.1 w hwK z hz y hy⟩
      intro he
      have hwS : w ∈ side K x d :=
        (mem_side K x d w).mpr ⟨hwK, he.trans hzd⟩
      have hzS : z ∈ side K x d :=
        (mem_side K x d z).mpr ⟨hz, hzd⟩
      exact hwz ((Finset.card_le_one.mp hs) w hwS z hzS)
    · intro he
      exact hoz (congrArg (fun f : X → Bool => f x) he)
  rcases cat_side_bound K x hc hx.1 with hf | ht
  · exact core false p q hp hq hpf
      (by rw [hqt, hpf]; decide) hf
  · exact core true q p hq hp hqt
      (by rw [hpf, hqt]; decide) ht

lemma mem_delta {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) :
    x ∈ delta K ↔
      ∃ u ∈ K, ∃ v ∈ K,
        u x ≠ v x ∧ ∀ y, x < y → u y = v y := by
  simp [delta]

lemma delta_mono {X : Type*} [LinearOrder X] [Fintype X]
    {A K : Finset (X → Bool)} (hAK : A ⊆ K) :
    delta A ⊆ delta K := by
  intro x hx
  obtain ⟨u, hu, v, hv, h⟩ := (mem_delta A x).mp hx
  exact (mem_delta K x).mpr ⟨u, hAK hu, v, hAK hv, h⟩

lemma delta_singleton {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) : delta ({z} : Finset (X → Bool)) = ∅ := by
  apply Finset.subset_empty.mp
  intro x hx
  obtain ⟨u, hu, v, hv, hne, _⟩ := (mem_delta _ x).mp hx
  exfalso
  apply hne
  rw [Finset.mem_singleton.mp hu, Finset.mem_singleton.mp hv]

lemma delta_insert_sub {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    delta (insert z A) ⊆ insert x (delta A) := by
  intro y hy
  obtain ⟨u, hu, v, hv, hne, hag⟩ := (mem_delta _ y).mp hy
  rcases Finset.mem_insert.mp hu with hu | hu
  · rcases Finset.mem_insert.mp hv with hv | hv
    · exact (hne (by rw [hu, hv])).elim
    · have hyx : y = x :=
        level_unique v z x y (hr v hv).1 (hr v hv).2
          (by rw [← hu]; exact hne.symm)
          (by intro t ht; rw [← hu]; exact (hag t ht).symm)
      rw [hyx]
      exact Finset.mem_insert_self _ _
  · rcases Finset.mem_insert.mp hv with hv | hv
    · have hyx : y = x :=
        level_unique u z x y (hr u hu).1 (hr u hu).2
          (by rw [← hv]; exact hne)
          (by intro t ht; rw [← hv]; exact hag t ht)
      rw [hyx]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        ((mem_delta A y).mpr ⟨u, hu, v, hv, hne, hag⟩)

lemma delta_insert_sup {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hA : A.Nonempty) :
    insert x (delta A) ⊆ delta (insert z A) := by
  intro y hy
  rcases Finset.mem_insert.mp hy with hy | hy
  · obtain ⟨w, hw⟩ := hA
    rw [hy]
    exact (mem_delta _ x).mpr
      ⟨w, Finset.mem_insert_of_mem hw, z, Finset.mem_insert_self _ _,
        (hr w hw).1, (hr w hw).2⟩
  · exact delta_mono (Finset.subset_insert z A) hy

lemma delta_notin {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    x ∉ delta A := by
  intro hx
  obtain ⟨u, hu, v, hv, hne, _⟩ := (mem_delta A x).mp hx
  exact hne (bool_eq (u x) (z x) (v x) (hr u hu).1 (hr v hv).1)

lemma delta_insert {X : Type*} [LinearOrder X] [Fintype X]
    (z : X → Bool) (A : Finset (X → Bool)) (x : X)
    (hr : ∀ w ∈ A, w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hA : A.Nonempty) :
    delta (insert z A) = insert x (delta A) :=
  Finset.Subset.antisymm
    (delta_insert_sub z A x hr) (delta_insert_sup z A x hr hA)

lemma delta_card {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool),
      K.card ≤ n → Cat K → K.card ≤ (delta K).card + 1 := by
  intro n
  induction n with
  | zero =>
      intro K hK _
      omega
  | succ n ih =>
      intro K hKn hc
      by_cases hsmall : K.card ≤ 1
      · omega
      obtain ⟨x, z, hz, hr, hne⟩ := peel K hc (by omega)
      have hs := delta_insert_sup z (K.erase z) x hr hne
      rw [Finset.insert_erase hz] at hs
      have hxn := delta_notin z (K.erase z) x hr
      have h1 := Finset.card_erase_of_mem hz
      have h2 := Finset.card_le_card hs
      rw [Finset.card_insert_of_notMem hxn] at h2
      have h3 := ih (K.erase z) (by omega)
        (cat_sub (Finset.erase_subset z K) hc)
      omega

lemma delta_real {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool),
      K.card ≤ n → Cat K → K.Nonempty →
      ∀ D : Finset X, D ⊆ delta K →
        ∃ A : Finset (X → Bool),
          A ⊆ K ∧ A.card = D.card + 1 ∧ delta A = D := by
  intro n
  induction n with
  | zero =>
      intro K hK _ hne D _
      have hp := Finset.card_pos.mpr hne
      omega
  | succ n ih =>
      intro K hKn hc hne D hD
      by_cases hDe : D = ∅
      · obtain ⟨z, hz⟩ := hne
        refine ⟨{z}, Finset.singleton_subset_iff.mpr hz, ?_, ?_⟩
        · simp [hDe]
        · rw [hDe]
          exact delta_singleton z
      obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hDe
      obtain ⟨u, hu, v, hv, huv, _⟩ :=
        (mem_delta K d).mp (hD hd)
      have huv' : u ≠ v := fun h =>
        huv (congrArg (fun f : X → Bool => f d) h)
      have hK2 : 2 ≤ K.card := by
        have hh : 1 < K.card :=
          Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv'⟩
        omega
      obtain ⟨x, z, hz, hr, hne'⟩ := peel K hc hK2
      have hcard : (K.erase z).card ≤ n := by
        have he := Finset.card_erase_of_mem hz
        omega
      have hc' : Cat (K.erase z) :=
        cat_sub (Finset.erase_subset z K) hc
      have hs : delta K ⊆ insert x (delta (K.erase z)) := by
        have hh := delta_insert_sub z (K.erase z) x hr
        rw [Finset.insert_erase hz] at hh
        exact hh
      by_cases hxD : x ∈ D
      · have hD' : D.erase x ⊆ delta (K.erase z) := by
          intro y hy
          obtain ⟨hyx, hyD⟩ := Finset.mem_erase.mp hy
          rcases Finset.mem_insert.mp (hs (hD hyD)) with he | he
          · exact (hyx he).elim
          · exact he
        obtain ⟨A, hA, hAc, hAd⟩ :=
          ih (K.erase z) hcard hc' hne' (D.erase x) hD'
        have hzA : z ∉ A := fun h =>
          (Finset.mem_erase.mp (hA h)).1 rfl
        have hAn : A.Nonempty := Finset.card_pos.mp (by omega)
        refine ⟨insert z A,
          Finset.insert_subset hz
            (hA.trans (Finset.erase_subset z K)), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hzA, hAc]
          have he := Finset.card_erase_of_mem hxD
          have hp := Finset.card_pos.mpr ⟨x, hxD⟩
          omega
        · rw [delta_insert z A x
            (fun w hw => hr w (hA hw)) hAn, hAd]
          exact Finset.insert_erase hxD
      · have hD' : D ⊆ delta (K.erase z) := by
          intro y hy
          rcases Finset.mem_insert.mp (hs (hD hy)) with he | he
          · exact (hxD (by rw [← he]; exact hy)).elim
          · exact he
        obtain ⟨A, hA, hAc, hAd⟩ :=
          ih (K.erase z) hcard hc' hne' D hD'
        exact ⟨A, hA.trans (Finset.erase_subset z K), hAc, hAd⟩

lemma cat_local {X : Type*} [LinearOrder X] [Fintype X]
    (m : ℕ) (hm : 4 ≤ m)
    (K : Finset (X → Bool)) (hKm : m ≤ K.card)
    (hall : ∀ A ⊆ K, A.card = m → Cat A) : Cat K := by
  intro u hu v hv w hw z hz x huv hwz hag huvx hwzx
  have hS : ({u, v, w, z} : Finset (X → Bool)) ⊆ K := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  have hSc : ({u, v, w, z} : Finset (X → Bool)).card ≤ m := by
    have h1 := Finset.card_insert_le u ({v, w, z} : Finset (X → Bool))
    have h2 := Finset.card_insert_le v ({w, z} : Finset (X → Bool))
    have h3 := Finset.card_insert_le w ({z} : Finset (X → Bool))
    rw [Finset.card_singleton] at h3
    omega
  obtain ⟨A, hSA, hAK, hAc⟩ := extend _ K m hS hSc hKm
  exact hall A hAK hAc
    u (hSA (by simp)) v (hSA (by simp))
    w (hSA (by simp)) z (hSA (by simp))
    x huv hwz hag huvx hwzx

lemma attach_side {X : Type*} [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) (hag : Above K x)
    (d : Bool) (z : X → Bool) (hz : z ∈ K) (hzd : z x ≠ d)
    (T : Finset (X → Bool)) (hT : T ⊆ side K x d) (hc : Cat T) :
    ∃ D : Finset (X → Bool),
      D ⊆ K ∧ Cat D ∧ D.card = T.card + 1 := by
  have hTK : T ⊆ K := hT.trans (side_sub K x d)
  have hzT : z ∉ T := fun h =>
    hzd ((mem_side K x d z).mp (hT h)).2
  have hr : ∀ w ∈ T,
      w x ≠ z x ∧ ∀ y, x < y → w y = z y := by
    intro w hw
    have hwd := ((mem_side K x d w).mp (hT hw)).2
    refine ⟨?_, fun y hy => hag w (hTK hw) z hz y hy⟩
    intro he
    exact hzd (he.symm.trans hwd)
  exact ⟨insert z T, Finset.insert_subset hz hTK,
    cat_insert z T x hr hc, Finset.card_insert_of_notMem hzT⟩

def NC {X : Type*} [LinearOrder X] [Fintype X]
    (A : Finset (X → Bool)) : Prop :=
  ∃ z : X → Bool, Cat (A.erase z)

noncomputable def colour {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C) (A : Finset (X → Bool)) : C :=
  if Cat A then χ (delta A) else if NC A then b else a

lemma colour_cat {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hc : Cat A) :
    colour a b χ A = χ (delta A) := by
  unfold colour
  rw [if_pos hc]

lemma colour_nc {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hc : ¬ Cat A) (hn : NC A) :
    colour a b χ A = b := by
  unfold colour
  rw [if_neg hc, if_pos hn]

lemma colour_else {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hc : ¬ Cat A) (hn : ¬ NC A) :
    colour a b χ A = a := by
  unfold colour
  rw [if_neg hc, if_neg hn]

lemma colour_noncat {X C : Type*} [LinearOrder X] [Fintype X]
    (a b : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hnc : ¬ Cat A) :
    colour a b χ A = a ∨ colour a b χ A = b := by
  by_cases h : NC A
  · exact Or.inr (colour_nc a b χ A hnc h)
  · exact Or.inl (colour_else a b χ A hnc h)

lemma cat_bound {X C : Type*} [LinearOrder X] [Fintype X]
    (k s : ℕ) (a b : C) (χ : Finset X → C) (i : C)
    (hχ : Solon.NoMono χ k s i)
    (K : Finset (X → Bool))
    (hm : ∀ A ⊆ K, A.card = k + 1 → colour a b χ A = i)
    (T : Finset (X → Bool)) (hTK : T ⊆ K) (hc : Cat T) :
    T.card ≤ s := by
  by_contra hbig
  have hd := delta_card T.card T (le_refl _) hc
  obtain ⟨S, hS, hSc⟩ :=
    Finset.exists_subset_card_eq
      (show s ≤ (delta T).card by omega)
  obtain ⟨D, hD, hDne⟩ := hχ S hSc
  obtain ⟨hDS, hDc⟩ := Finset.mem_powersetCard.mp hD
  have hTn : T.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hAT, hAc, hAd⟩ :=
    delta_real T.card T (le_refl _) hc hTn D (hDS.trans hS)
  have he := hm A (hAT.trans hTK) (by rw [hAc, hDc])
  rw [colour_cat a b χ A (cat_sub hAT hc), hAd] at he
  exact hDne he

lemma nc_sub {X : Type*} [LinearOrder X] [Fintype X]
    {A B : Finset (X → Bool)} (hBA : B ⊆ A) (h : NC A) : NC B := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z, cat_sub ?_ hz⟩
  intro y hy
  obtain ⟨hne, hyB⟩ := Finset.mem_erase.mp hy
  exact Finset.mem_erase.mpr ⟨hne, hBA hyB⟩

lemma small_nc {X C : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (a b : C) (hab : a ≠ b) (χ : Finset X → C)
    (K : Finset (X → Bool)) (hKk : k + 1 ≤ K.card)
    (hm : ∀ A ⊆ K, A.card = k + 1 → colour a b χ A = b)
    (B : Finset (X → Bool)) (hBK : B ⊆ K) (hB : B.card ≤ k + 1) :
    NC B := by
  obtain ⟨A, hBA, hAK, hAc⟩ := extend B K (k + 1) hBK hB hKk
  by_contra hnB
  have hnA : ¬ NC A := fun h => hnB (nc_sub hBA h)
  have hcA : ¬ Cat A := fun h =>
    hnA ⟨fun _ => false, cat_sub (Finset.erase_subset _ _) h⟩
  exact hab ((colour_else a b χ A hcA hnA).symm.trans (hm A hAK hAc))

lemma no_bal {X : Type*} [LinearOrder X]
    (S : Finset (X → Bool)) (hS : Cat S) (x : X)
    (hag : ∀ u ∈ S, ∀ v ∈ S, ∀ y, x < y → u y = v y)
    (d e : Bool) (hde : d ≠ e)
    (p1 p2 q1 q2 : X → Bool)
    (hp1 : p1 ∈ S) (hp2 : p2 ∈ S) (hq1 : q1 ∈ S) (hq2 : q2 ∈ S)
    (hp : p1 ≠ p2) (hq : q1 ≠ q2)
    (h1 : p1 x = d) (h2 : p2 x = d) (h3 : q1 x = e) (h4 : q2 x = e) :
    False := by
  have hh := hS p1 hp1 p2 hp2 q1 hq1 q2 hq2 x hp hq
    (fun y hy => ⟨hag p1 hp1 q1 hq1 y hy, hag p2 hp2 q1 hq1 y hy,
      hag q2 hq2 q1 hq1 y hy⟩)
    (h1.trans h2.symm) (h3.trans h4.symm)
  exact hde (h1.symm.trans (hh.trans h3))

lemma other_cat {X : Type*} [LinearOrder X] [Fintype X]
    (Q : Finset (X → Bool)) (x : X) (hag : Above Q x)
    (hall : ∀ B ⊆ Q, B.card ≤ 6 → NC B)
    (d e : Bool) (hde : d ≠ e)
    (hL : (side Q x d).card = 2) : Cat (side Q x e) := by
  intro u hu v hv w hw t ht y huv hwt hagy huvy hwty
  by_contra hne
  obtain ⟨u1, u2, h12, hS⟩ := Finset.card_eq_two.mp hL
  have hu1 : u1 ∈ side Q x d := by rw [hS]; simp
  have hu2 : u2 ∈ side Q x d := by rw [hS]; simp
  obtain ⟨hu1Q, hu1d⟩ := (mem_side Q x d u1).mp hu1
  obtain ⟨hu2Q, hu2d⟩ := (mem_side Q x d u2).mp hu2
  obtain ⟨huQ, hue⟩ := (mem_side Q x e u).mp hu
  obtain ⟨hvQ, hve⟩ := (mem_side Q x e v).mp hv
  obtain ⟨hwQ, hwe⟩ := (mem_side Q x e w).mp hw
  obtain ⟨htQ, hte⟩ := (mem_side Q x e t).mp ht
  have huw : u ≠ w := fun h => hne (by rw [h])
  have hut : u ≠ t := fun h => hne (by rw [h]; exact hwty.symm)
  have hvw : v ≠ w := fun h => hne (by rw [huvy, h])
  have hvt : v ≠ t := fun h => hne (by rw [huvy, h]; exact hwty.symm)
  obtain ⟨B, hB⟩ : ∃ B : Finset (X → Bool),
      B = insert u1 (insert u2 (insert u (insert v (insert w {t})))) :=
    ⟨_, rfl⟩
  have hmB : ∀ r, (r = u1 ∨ r = u2 ∨ r = u ∨ r = v ∨ r = w ∨ r = t) →
      r ∈ B := by
    intro r hr
    rw [hB]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hr
  have hBQ : B ⊆ Q := by
    intro r hr
    rw [hB] at hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with h | h | h | h | h | h <;> rw [h] <;> assumption
  have hBc : B.card ≤ 6 := by
    rw [hB]
    have h1 := Finset.card_insert_le u1
      (insert u2 (insert u (insert v (insert w ({t} : Finset (X → Bool))))))
    have h2 := Finset.card_insert_le u2
      (insert u (insert v (insert w ({t} : Finset (X → Bool)))))
    have h3 := Finset.card_insert_le u
      (insert v (insert w ({t} : Finset (X → Bool))))
    have h4 := Finset.card_insert_le v
      (insert w ({t} : Finset (X → Bool)))
    have h5 := Finset.card_insert_le w ({t} : Finset (X → Bool))
    rw [Finset.card_singleton] at h5
    omega
  obtain ⟨z, hz⟩ := hall B hBQ hBc
  have hE : ∀ r, (r = u1 ∨ r = u2 ∨ r = u ∨ r = v ∨ r = w ∨ r = t) →
      r ≠ z → r ∈ B.erase z :=
    fun r hr hrz => Finset.mem_erase.mpr ⟨hrz, hmB r hr⟩
  have hagE : ∀ p ∈ B.erase z, ∀ q ∈ B.erase z, ∀ y', x < y' →
      p y' = q y' :=
    fun p hp q hq y' hy' =>
      hag p (hBQ (Finset.mem_of_mem_erase hp))
        q (hBQ (Finset.mem_of_mem_erase hq)) y' hy'
  have hd1 : ∀ r : X → Bool, r x = e → u1 ≠ r := by
    intro r hr h
    apply hde
    rw [← hu1d, h]
    exact hr
  have hd2 : ∀ r : X → Bool, r x = e → u2 ≠ r := by
    intro r hr h
    apply hde
    rw [← hu2d, h]
    exact hr
  have m1 : u1 = u1 ∨ u1 = u2 ∨ u1 = u ∨ u1 = v ∨ u1 = w ∨ u1 = t :=
    Or.inl rfl
  have m2 : u2 = u1 ∨ u2 = u2 ∨ u2 = u ∨ u2 = v ∨ u2 = w ∨ u2 = t :=
    Or.inr (Or.inl rfl)
  have mu : u = u1 ∨ u = u2 ∨ u = u ∨ u = v ∨ u = w ∨ u = t :=
    Or.inr (Or.inr (Or.inl rfl))
  have mv : v = u1 ∨ v = u2 ∨ v = u ∨ v = v ∨ v = w ∨ v = t :=
    Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have mw : w = u1 ∨ w = u2 ∨ w = u ∨ w = v ∨ w = w ∨ w = t :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have mt : t = u1 ∨ t = u2 ∨ t = u ∨ t = v ∨ t = w ∨ t = t :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  by_cases hz1 : z = u ∨ z = v
  · have hze : z x = e := by
      rcases hz1 with h | h
      · rw [h]; exact hue
      · rw [h]; exact hve
    have hwz : w ≠ z := by
      intro h
      rcases hz1 with h' | h'
      · exact huw (h'.symm.trans h.symm)
      · exact hvw (h'.symm.trans h.symm)
    have htz : t ≠ z := by
      intro h
      rcases hz1 with h' | h'
      · exact hut (h'.symm.trans h.symm)
      · exact hvt (h'.symm.trans h.symm)
    exact no_bal (B.erase z) hz x hagE d e hde u1 u2 w t
      (hE u1 m1 (hd1 z hze)) (hE u2 m2 (hd2 z hze))
      (hE w mw hwz) (hE t mt htz) h12 hwt hu1d hu2d hwe hte
  · by_cases hz2 : z = w ∨ z = t
    · have hze : z x = e := by
        rcases hz2 with h | h
        · rw [h]; exact hwe
        · rw [h]; exact hte
      have huz : u ≠ z := by
        intro h
        rcases hz2 with h' | h'
        · exact huw (h.trans h')
        · exact hut (h.trans h')
      have hvz : v ≠ z := by
        intro h
        rcases hz2 with h' | h'
        · exact hvw (h.trans h')
        · exact hvt (h.trans h')
      exact no_bal (B.erase z) hz x hagE d e hde u1 u2 u v
        (hE u1 m1 (hd1 z hze)) (hE u2 m2 (hd2 z hze))
        (hE u mu huz) (hE v mv hvz) h12 huv hu1d hu2d hue hve
    · have huz : u ≠ z := fun h => hz1 (Or.inl h.symm)
      have hvz : v ≠ z := fun h => hz1 (Or.inr h.symm)
      have hwz : w ≠ z := fun h => hz2 (Or.inl h.symm)
      have htz : t ≠ z := fun h => hz2 (Or.inr h.symm)
      exact hne (hz u (hE u mu huz) v (hE v mv hvz)
        w (hE w mw hwz) t (hE t mt htz) y huv hwt hagy huvy hwty)

lemma close_b {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ n : ℕ, ∀ Q : Finset (X → Bool), Q.card ≤ n →
      (∀ B ⊆ Q, B.card ≤ 6 → NC B) →
      ∃ D : Finset (X → Bool), D ⊆ Q ∧ Cat D ∧ Q.card ≤ D.card + 1 := by
  intro n
  induction n with
  | zero =>
      intro Q hQ _
      exact ⟨Q, Finset.Subset.refl Q, cat_small Q (by omega), by omega⟩
  | succ n ih =>
      intro Q hQn hall
      by_cases hsmall : Q.card ≤ 1
      · exact ⟨Q, Finset.Subset.refl Q, cat_small Q (by omega), by omega⟩
      obtain ⟨x, hx⟩ := top Q (by omega)
      obtain ⟨p, hp, hpf, q, hq, hqt⟩ := split_points hx
      have hsum := side_cards Q x
      have hLn : 0 < (side Q x false).card :=
        Finset.card_pos.mpr ⟨p, (mem_side Q x false p).mpr ⟨hp, hpf⟩⟩
      have hRn : 0 < (side Q x true).card :=
        Finset.card_pos.mpr ⟨q, (mem_side Q x true q).mpr ⟨hq, hqt⟩⟩
      by_cases hL1 : (side Q x false).card ≤ 1
      · obtain ⟨T, hTR, hc, hTc⟩ := ih (side Q x true) (by omega)
          (fun B hB hBc => hall B (hB.trans (side_sub Q x true)) hBc)
        obtain ⟨D, hDQ, hDc, hDcard⟩ :=
          attach_side Q x hx.1 true p hp (by rw [hpf]; decide) T hTR hc
        exact ⟨D, hDQ, hDc, by omega⟩
      by_cases hR1 : (side Q x true).card ≤ 1
      · obtain ⟨T, hTL, hc, hTc⟩ := ih (side Q x false) (by omega)
          (fun B hB hBc => hall B (hB.trans (side_sub Q x false)) hBc)
        obtain ⟨D, hDQ, hDc, hDcard⟩ :=
          attach_side Q x hx.1 false q hq (by rw [hqt]; decide) T hTL hc
        exact ⟨D, hDQ, hDc, by omega⟩
      by_cases hL2 : (side Q x false).card = 2
      · have hc := other_cat Q x hx.1 hall false true (by decide) hL2
        obtain ⟨D, hDQ, hDc, hDcard⟩ :=
          attach_side Q x hx.1 true p hp (by rw [hpf]; decide)
            (side Q x true) (Finset.Subset.refl _) hc
        exact ⟨D, hDQ, hDc, by omega⟩
      by_cases hR2 : (side Q x true).card = 2
      · have hc := other_cat Q x hx.1 hall true false (by decide) hR2
        obtain ⟨D, hDQ, hDc, hDcard⟩ :=
          attach_side Q x hx.1 false q hq (by rw [hqt]; decide)
            (side Q x false) (Finset.Subset.refl _) hc
        exact ⟨D, hDQ, hDc, by omega⟩
      exfalso
      obtain ⟨P, hPL, hPc⟩ := Finset.exists_subset_card_eq
        (show 3 ≤ (side Q x false).card by omega)
      obtain ⟨T, hTR, hTc⟩ := Finset.exists_subset_card_eq
        (show 3 ≤ (side Q x true).card by omega)
      have hPQ : P ⊆ Q := hPL.trans (side_sub Q x false)
      have hTQ : T ⊆ Q := hTR.trans (side_sub Q x true)
      have hBQ : P ∪ T ⊆ Q := Finset.union_subset hPQ hTQ
      have hBc : (P ∪ T).card ≤ 6 := by
        have := Finset.card_union_le P T
        omega
      obtain ⟨z, hz⟩ := hall (P ∪ T) hBQ hBc
      have hPe : P.card - 1 ≤ (P.erase z).card :=
        Finset.pred_card_le_card_erase
      have hTe : T.card - 1 ≤ (T.erase z).card :=
        Finset.pred_card_le_card_erase
      obtain ⟨p1, hp1, p2, hp2, hp12⟩ := two_points (P.erase z) (by omega)
      obtain ⟨q1, hq1, q2, hq2, hq12⟩ := two_points (T.erase z) (by omega)
      have hsP : ∀ r ∈ P.erase z, r ∈ (P ∪ T).erase z := fun r hr =>
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1,
          Finset.mem_union_left _ (Finset.mem_erase.mp hr).2⟩
      have hsT : ∀ r ∈ T.erase z, r ∈ (P ∪ T).erase z := fun r hr =>
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1,
          Finset.mem_union_right _ (Finset.mem_erase.mp hr).2⟩
      have hbP : ∀ r ∈ P.erase z, r x = false := fun r hr =>
        ((mem_side Q x false r).mp (hPL (Finset.mem_of_mem_erase hr))).2
      have hbT : ∀ r ∈ T.erase z, r x = true := fun r hr =>
        ((mem_side Q x true r).mp (hTR (Finset.mem_of_mem_erase hr))).2
      have hagE : ∀ u ∈ (P ∪ T).erase z, ∀ v ∈ (P ∪ T).erase z,
          ∀ y, x < y → u y = v y :=
        fun u hu v hv y hy =>
          hx.1 u (hBQ (Finset.mem_of_mem_erase hu))
            v (hBQ (Finset.mem_of_mem_erase hv)) y hy
      exact no_bal ((P ∪ T).erase z) hz x hagE false true (by decide)
        p1 p2 q1 q2 (hsP p1 hp1) (hsP p2 hp2) (hsT q1 hq1) (hsT q2 hq2)
        hp12 hq12 (hbP p1 hp1) (hbP p2 hp2) (hbT q1 hq1) (hbT q2 hq2)

lemma big_cat {X : Type*} [LinearOrder X] [Fintype X] :
    ∀ m : ℕ, ∀ Q : Finset (X → Bool), 2 ^ m < Q.card →
      ∃ D : Finset (X → Bool), D ⊆ Q ∧ Cat D ∧ m + 2 ≤ D.card := by
  intro m
  induction m with
  | zero =>
      intro Q hQ
      rw [pow_zero] at hQ
      obtain ⟨u, hu, v, hv, huv⟩ := two_points Q (by omega)
      have hc2 := Finset.card_pair huv
      refine ⟨{u, v}, ?_, cat_small _ (by omega), by omega⟩
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with h | h <;> rw [h] <;> assumption
  | succ m ih =>
      intro Q hQ
      obtain ⟨t, ht⟩ : ∃ t, t = 2 ^ m := ⟨_, rfl⟩
      have hQ' : t * 2 < Q.card := by
        rw [ht, ← pow_succ]
        exact hQ
      have ht1 : 0 < t := by
        rw [ht]
        positivity
      obtain ⟨x, hx⟩ := top Q (by omega)
      obtain ⟨p, hp, hpf, q, hq, hqt⟩ := split_points hx
      have hsum := side_cards Q x
      by_cases hR : t < (side Q x true).card
      · obtain ⟨D, hDR, hc, hDc⟩ :=
          ih (side Q x true) (by rw [← ht]; exact hR)
        obtain ⟨D', hD'Q, hD'c, hD'card⟩ :=
          attach_side Q x hx.1 true p hp (by rw [hpf]; decide) D hDR hc
        exact ⟨D', hD'Q, hD'c, by omega⟩
      · have hL : t < (side Q x false).card := by omega
        obtain ⟨D, hDL, hc, hDc⟩ :=
          ih (side Q x false) (by rw [← ht]; exact hL)
        obtain ⟨D', hD'Q, hD'c, hD'card⟩ :=
          attach_side Q x hx.1 false q hq (by rw [hqt]; decide) D hDL hc
        exact ⟨D', hD'Q, hD'c, by omega⟩

lemma near_from_big {X : Type*} [LinearOrder X] [Fintype X]
    (k : ℕ) (hk : 4 ≤ k) (K : Finset (X → Bool)) (hK : ¬ Cat K)
    (D : Finset (X → Bool)) (hDK : D ⊆ K) (hD : Cat D) (hDk : k ≤ D.card) :
    ∃ A : Finset (X → Bool), A ⊆ K ∧ A.card = k + 1 ∧ ¬ Cat A ∧ NC A := by
  obtain ⟨S, hSdef⟩ : ∃ S : Finset (Finset (X → Bool)),
      S = K.powerset.filter (fun T => Cat T) := ⟨_, rfl⟩
  have hmemS : ∀ T, T ∈ S ↔ T ⊆ K ∧ Cat T := by
    intro T
    rw [hSdef, Finset.mem_filter, Finset.mem_powerset]
  obtain ⟨T, hTS, hmax⟩ :=
    Finset.exists_max_image S Finset.card ⟨D, (hmemS D).mpr ⟨hDK, hD⟩⟩
  obtain ⟨hTK, hTc⟩ := (hmemS T).mp hTS
  have hDT := hmax D ((hmemS D).mpr ⟨hDK, hD⟩)
  have hp : ∃ p ∈ K, p ∉ T := by
    by_contra h
    apply hK
    apply cat_sub _ hTc
    intro r hr
    by_contra hrT
    exact h ⟨r, hr, hrT⟩
  obtain ⟨p, hpK, hpT⟩ := hp
  by_contra hno
  have hcat : Cat (insert p T) := by
    intro u hu v hv w hw t ht y huv hwt hagy huvy hwty
    by_contra hne
    obtain ⟨F, hF⟩ : ∃ F : Finset (X → Bool),
        F = insert u (insert v (insert w {t})) := ⟨_, rfl⟩
    have hFsub : F ⊆ insert p T := by
      intro r hr
      rw [hF] at hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with h | h | h | h <;> rw [h] <;> assumption
    have hFc : F.card ≤ 4 := by
      rw [hF]
      have h1 := Finset.card_insert_le u
        (insert v (insert w ({t} : Finset (X → Bool))))
      have h2 := Finset.card_insert_le v (insert w ({t} : Finset (X → Bool)))
      have h3 := Finset.card_insert_le w ({t} : Finset (X → Bool))
      rw [Finset.card_singleton] at h3
      omega
    have hF0 : F.erase p ⊆ T := by
      intro r hr
      obtain ⟨hrp, hrF⟩ := Finset.mem_erase.mp hr
      exact (Finset.mem_insert.mp (hFsub hrF)).resolve_left hrp
    have hF0c : (F.erase p).card ≤ k := by
      have : (F.erase p).card ≤ F.card := Finset.card_erase_le
      omega
    obtain ⟨C', hFC, hCT, hCc⟩ := extend (F.erase p) T k hF0 hF0c (by omega)
    have hpC : p ∉ C' := fun h => hpT (hCT h)
    apply hno
    refine ⟨insert p C', Finset.insert_subset hpK (hCT.trans hTK), ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hpC, hCc]
    · intro hcA
      have hin : ∀ r ∈ F, r ∈ insert p C' := by
        intro r hr
        by_cases hrp : r = p
        · rw [hrp]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hFC (Finset.mem_erase.mpr ⟨hrp, hr⟩))
      have huF : u ∈ F := by rw [hF]; simp
      have hvF : v ∈ F := by rw [hF]; simp
      have hwF : w ∈ F := by rw [hF]; simp
      have htF : t ∈ F := by rw [hF]; simp
      exact hne (hcA u (hin u huF) v (hin v hvF) w (hin w hwF) t (hin t htF)
        y huv hwt hagy huvy hwty)
    · refine ⟨p, ?_⟩
      rw [Finset.erase_insert hpC]
      exact cat_sub hCT hTc
  have hle := hmax (insert p T)
    ((hmemS _).mpr ⟨Finset.insert_subset hpK hTK, hcat⟩)
  rw [Finset.card_insert_of_notMem hpT] at hle
  omega

end NearCatFive

theorem near_caterpillar_stepping_up_from_five : ∀ {X C : Type*} [LinearOrder X] [Fintype X] [DecidableEq C] (k : ℕ), 5 ≤ k → ∀ (a b : C), a ≠ b → ∀ (s : C → ℕ), (∀ i, k ≤ s i) → ∀ χ : Finset X → C, (∀ i, Solon.NoMono χ k (s i) i) → ∃ ψ : Finset (X → Bool) → C, Solon.NoMono ψ (k + 1) (max (s a + 1) (2 ^ (k - 2) + 1)) a ∧ Solon.NoMono ψ (k + 1) (s b + 2) b ∧ ∀ i, i ≠ a → i ≠ b → Solon.NoMono ψ (k + 1) (s i + 1) i := by
  intro X C _ _ _ k hk a b hab s hs χ hχ
  refine ⟨NearCatFive.colour a b χ, ?_, ?_, ?_⟩
  · intro K hK
    by_contra hn
    have hm : ∀ A ⊆ K, A.card = k + 1 → NearCatFive.colour a b χ A = a := by
      intro A hA hAc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hAc⟩, hne⟩
    have h1 : s a + 1 ≤ K.card := by
      rw [hK]
      exact le_max_left _ _
    have h2 : 2 ^ (k - 2) + 1 ≤ K.card := by
      rw [hK]
      exact le_max_right _ _
    by_cases hc : NearCatFive.Cat K
    · have hb := NearCatFive.cat_bound k (s a) a b χ a (hχ a) K hm K
        (Finset.Subset.refl K) hc
      omega
    · obtain ⟨D, hDK, hD, hDc⟩ :=
        NearCatFive.big_cat (k - 2) K (Nat.lt_of_succ_le h2)
      obtain ⟨A, hAK, hAc, hAn, hAN⟩ :=
        NearCatFive.near_from_big k (by omega) K hc D hDK hD (by omega)
      exact hab ((hm A hAK hAc).symm.trans
        (NearCatFive.colour_nc a b χ A hAn hAN))
  · intro K hK
    by_contra hn
    have hm : ∀ A ⊆ K, A.card = k + 1 → NearCatFive.colour a b χ A = b := by
      intro A hA hAc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hAc⟩, hne⟩
    have hsb := hs b
    have hall : ∀ B ⊆ K, B.card ≤ 6 → NearCatFive.NC B := fun B hB hBc =>
      NearCatFive.small_nc k a b hab χ K (by omega) hm B hB (by omega)
    obtain ⟨D, hDK, hD, hDc⟩ := NearCatFive.close_b K.card K (le_refl _) hall
    have hb := NearCatFive.cat_bound k (s b) a b χ b (hχ b) K hm D hDK hD
    omega
  · intro i hia hib K hK
    by_contra hn
    have hm : ∀ A ⊆ K, A.card = k + 1 → NearCatFive.colour a b χ A = i := by
      intro A hA hAc
      by_contra hne
      exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hA, hAc⟩, hne⟩
    have hsi := hs i
    have hc : NearCatFive.Cat K := by
      apply NearCatFive.cat_local (k + 1) (by omega) K (by omega)
      intro A hAK hAc
      by_contra hnc
      rcases NearCatFive.colour_noncat a b χ A hnc with he | he
      · exact hia ((hm A hAK hAc).symm.trans he)
      · exact hib ((hm A hAK hAc).symm.trans he)
    have hb := NearCatFive.cat_bound k (s i) a b χ i (hχ i) K hm K
      (Finset.Subset.refl K) hc
    omega

