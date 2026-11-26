import Proofs.Defs

set_option maxHeartbeats 0

namespace FallbackStep

lemma bool_other :
    ∀ p q r : Bool, p ≠ q → r ≠ q → p = r := by
  decide

lemma bool_different :
    ∀ p q : Bool, p ≠ q →
      (p = false ∧ q = true) ∨
      (p = true ∧ q = false) := by
  decide

lemma extend {V : Type*} [DecidableEq V]
    (S K : Finset V) (n : ℕ)
    (hSK : S ⊆ K) (hSn : S.card ≤ n) (hnK : n ≤ K.card) :
    ∃ A : Finset V, S ⊆ A ∧ A ⊆ K ∧ A.card = n := by
  have he := Finset.card_sdiff_add_card_eq_card hSK
  obtain ⟨R, hR, hRc⟩ :=
    Finset.exists_subset_card_eq
      (show n - S.card ≤ (K \ S).card by omega)
  have hd : Disjoint S R := by
    rw [Finset.disjoint_left]
    intro v hvS hvR
    exact (Finset.mem_sdiff.mp (hR hvR)).2 hvS
  refine ⟨S ∪ R, ?_, ?_, ?_⟩
  · exact fun v hv => Finset.mem_union_left R hv
  · exact Finset.union_subset hSK
      (fun v hv => (Finset.mem_sdiff.mp (hR hv)).1)
  · rw [Finset.card_union_of_disjoint hd]
    omega

lemma two_points {V : Type*} [DecidableEq V]
    (K : Finset V) (hK : 2 ≤ K.card) :
    ∃ u ∈ K, ∃ v ∈ K, u ≠ v := by
  obtain ⟨A, hAK, hAc⟩ := Finset.exists_subset_card_eq hK
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hAc
  exact ⟨u, hAK (Finset.mem_insert_self u {v}), v,
    hAK (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)), huv⟩

def Cat {X : Type*} [LinearOrder X]
    (K : Finset (X → Bool)) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, ∀ w ∈ K, ∀ z ∈ K, ∀ x : X,
    u ≠ v → w ≠ z →
    (∀ y, x < y →
      u y = v y ∧ u y = w y ∧ u y = z y) →
    u x = v x → w x = z x → u x = w x

noncomputable def levels {X : Type*}
    [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) : Finset X := by
  classical
  exact Finset.univ.filter (fun x =>
    ∃ u ∈ K, ∃ v ∈ K,
      u x ≠ v x ∧ ∀ y, x < y → u y = v y)

noncomputable def color {X C : Type*}
    [LinearOrder X] [Fintype X]
    (a : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) : C := by
  classical
  exact if Cat A then χ (levels A) else a

lemma mem_levels {X : Type*}
    [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool)) (x : X) :
    x ∈ levels K ↔
      ∃ u ∈ K, ∃ v ∈ K,
        u x ≠ v x ∧ ∀ y, x < y → u y = v y := by
  classical
  simp only [levels, Finset.mem_filter, Finset.mem_univ, true_and]

lemma levels_mono {X : Type*}
    [LinearOrder X] [Fintype X]
    {A B : Finset (X → Bool)} (hAB : A ⊆ B) :
    levels A ⊆ levels B := by
  intro x hx
  obtain ⟨u, hu, v, hv, hne, hag⟩ := (mem_levels A x).mp hx
  exact (mem_levels B x).mpr
    ⟨u, hAB hu, v, hAB hv, hne, hag⟩

lemma highest_unique {X : Type*} [LinearOrder X]
    (u v : X → Bool) (x y : X)
    (hx : u x ≠ v x)
    (hxa : ∀ z, x < z → u z = v z)
    (hy : u y ≠ v y)
    (hya : ∀ z, y < z → u z = v z) :
    y = x := by
  rcases lt_trichotomy x y with h | h | h
  · exact (hy (hxa y h)).elim
  · exact h.symm
  · exact (hx (hya x h)).elim

lemma top {X : Type*}
    [LinearOrder X] [Fintype X]
    (K : Finset (X → Bool))
    (u v : X → Bool) (hu : u ∈ K) (hv : v ∈ K)
    (huv : u ≠ v) :
    ∃ x : X,
      (∀ p ∈ K, ∀ q ∈ K, ∀ y, x < y → p y = q y) ∧
      ∃ p ∈ K, ∃ q ∈ K, p x ≠ q x := by
  classical
  let S : Finset X := Finset.univ.filter
    (fun x => ∃ p ∈ K, ∃ q ∈ K, p x ≠ q x)
  have hm : ∀ x : X,
      x ∈ S ↔ ∃ p ∈ K, ∃ q ∈ K, p x ≠ q x := by
    intro x
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hS : S.Nonempty := by
    by_contra hn
    apply huv
    funext x
    by_contra hx
    exact hn ⟨x, (hm x).mpr ⟨u, hu, v, hv, hx⟩⟩
  obtain ⟨x, hx, hmax⟩ :=
    Finset.exists_max_image S (fun x : X => x) hS
  refine ⟨x, ?_, (hm x).mp hx⟩
  intro p hp q hq y hxy
  by_contra hne
  have hy : y ∈ S := (hm y).mpr ⟨p, hp, q, hq, hne⟩
  exact (not_le.mpr hxy) (hmax y hy)

lemma cat_sub {X : Type*} [LinearOrder X]
    {A K : Finset (X → Bool)}
    (hAK : A ⊆ K) (hK : Cat K) : Cat A := by
  intro u hu v hv w hw z hz
  exact hK u (hAK hu) v (hAK hv) w (hAK hw) z (hAK hz)

lemma cat_pair {X : Type*} [LinearOrder X]
    [DecidableEq (X → Bool)] (p q : X → Bool) :
    Cat ({p, q} : Finset (X → Bool)) := by
  intro u hu v hv w hw z hz x huv hwz hag hbit hbit'
  have hm : ∀ r ∈ ({p, q} : Finset (X → Bool)),
      r = p ∨ r = q := by
    intro r hr
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hr
  rcases hm u hu with h1 | h1 <;>
    rcases hm v hv with h2 | h2 <;>
    rcases hm w hw with h3 | h3 <;>
    first
      | exact (huv (h1.trans h2.symm)).elim
      | exact congrArg (fun r : X → Bool => r x)
          (h1.trans h3.symm)
      | exact hbit.trans
          (congrArg (fun r : X → Bool => r x)
            (h2.trans h3.symm))

lemma cat_insert {X : Type*} [LinearOrder X]
    [DecidableEq (X → Bool)]
    (tip : X → Bool) (K : Finset (X → Bool)) (x : X)
    (hrest : ∀ w ∈ K,
      w x ≠ tip x ∧ ∀ y, x < y → w y = tip y)
    (hK : Cat K) :
    Cat (insert tip K) := by
  have mem_old : ∀ p ∈ insert tip K, p ≠ tip → p ∈ K := by
    intro p hp hn
    rcases Finset.mem_insert.mp hp with he | he
    · exact (hn he).elim
    · exact he
  have unique : ∀ p ∈ insert tip K, p x = tip x → p = tip := by
    intro p hp he
    rcases Finset.mem_insert.mp hp with ht | hk
    · exact ht
    · exact ((hrest p hk).1 he).elim
  have above : ∀ p ∈ insert tip K, ∀ y,
      x < y → p y = tip y := by
    intro p hp y hy
    rcases Finset.mem_insert.mp hp with ht | hk
    · rw [ht]
    · exact (hrest p hk).2 y hy
  intro u hu v hv w hw z hz r huv hwz hag hbit hbit'
  rcases lt_trichotomy x r with hxr | hxr | hrx
  · exact (above u hu r hxr).trans (above w hw r hxr).symm
  · subst r
    have hun : u x ≠ tip x := by
      intro he
      have hvx : v x = tip x := hbit.symm.trans he
      exact huv ((unique u hu he).trans (unique v hv hvx).symm)
    have hwn : w x ≠ tip x := by
      intro he
      have hzx : z x = tip x := hbit'.symm.trans he
      exact hwz ((unique w hw he).trans (unique z hz hzx).symm)
    exact bool_other (u x) (tip x) (w x) hun hwn
  · have he := hag x hrx
    have huK : u ∈ K := by
      apply mem_old u hu
      intro hut
      have hvx : v x = tip x :=
        he.1.symm.trans
          (congrArg (fun p : X → Bool => p x) hut)
      exact huv (hut.trans (unique v hv hvx).symm)
    have hun : u x ≠ tip x := (hrest u huK).1
    have hvK : v ∈ K := by
      apply mem_old v hv
      intro hvt
      exact hun (he.1.trans
        (congrArg (fun p : X → Bool => p x) hvt))
    have hwK : w ∈ K := by
      apply mem_old w hw
      intro hwt
      exact hun (he.2.1.trans
        (congrArg (fun p : X → Bool => p x) hwt))
    have hzK : z ∈ K := by
      apply mem_old z hz
      intro hzt
      exact hun (he.2.2.trans
        (congrArg (fun p : X → Bool => p x) hzt))
    exact hK u huK v hvK w hwK z hzK r
      huv hwz hag hbit hbit'

lemma peel {X : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)]
    (K : Finset (X → Bool)) (hK : Cat K)
    (u v : X → Bool) (hu : u ∈ K) (hv : v ∈ K)
    (huv : u ≠ v) :
    ∃ x : X, ∃ z ∈ K,
      (∀ w ∈ K.erase z,
        w x ≠ z x ∧ ∀ y, x < y → w y = z y) ∧
      (K.erase z).Nonempty := by
  classical
  obtain ⟨x, hag, p, hp, q, hq, hpq⟩ :=
    top K u v hu hv huv
  have hs : ∃ z ∈ K, ∀ w ∈ K, w ≠ z → w x ≠ z x := by
    by_contra hn
    have hp2 : ∃ p2 ∈ K, p2 ≠ p ∧ p2 x = p x := by
      by_contra h
      exact hn ⟨p, hp, fun w hw hwp he =>
        h ⟨w, hw, hwp, he⟩⟩
    have hq2 : ∃ q2 ∈ K, q2 ≠ q ∧ q2 x = q x := by
      by_contra h
      exact hn ⟨q, hq, fun w hw hwq he =>
        h ⟨w, hw, hwq, he⟩⟩
    obtain ⟨p2, hp2K, hp2p, hp2x⟩ := hp2
    obtain ⟨q2, hq2K, hq2q, hq2x⟩ := hq2
    have he := hK p hp p2 hp2K q hq q2 hq2K x
      (Ne.symm hp2p) (Ne.symm hq2q)
      (fun y hy =>
        ⟨hag p hp p2 hp2K y hy,
         hag p hp q hq y hy,
         hag p hp q2 hq2K y hy⟩)
      hp2x.symm hq2x.symm
    exact hpq he
  obtain ⟨z, hz, hzonly⟩ := hs
  refine ⟨x, z, hz, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwz, hwK⟩ := Finset.mem_erase.mp hw
    exact ⟨hzonly w hwK hwz,
      fun y hy => hag w hwK z hz y hy⟩
  · by_cases huz : u = z
    · refine ⟨v, Finset.mem_erase.mpr ⟨?_, hv⟩⟩
      intro hvz
      exact huv (huz.trans hvz.symm)
    · exact ⟨u, Finset.mem_erase.mpr ⟨huz, hu⟩⟩

lemma levels_singleton {X : Type*}
    [LinearOrder X] [Fintype X]
    (u : X → Bool) :
    levels ({u} : Finset (X → Bool)) = ∅ := by
  apply Finset.subset_empty.mp
  intro x hx
  obtain ⟨v, hv, w, hw, hne, hag⟩ :=
    (mem_levels {u} x).mp hx
  have he : v x = w x := by
    rw [Finset.mem_singleton.mp hv, Finset.mem_singleton.mp hw]
  exact (hne he).elim

lemma levels_insert_sub {X : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)]
    (z : X → Bool) (K : Finset (X → Bool)) (x : X)
    (hrest : ∀ w ∈ K,
      w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    levels (insert z K) ⊆ insert x (levels K) := by
  intro y hy
  obtain ⟨u, hu, v, hv, hne, hag⟩ :=
    (mem_levels (insert z K) y).mp hy
  rcases Finset.mem_insert.mp hu with huz | huK
  · rcases Finset.mem_insert.mp hv with hvz | hvK
    · exact (hne (by rw [huz, hvz])).elim
    · have hr := hrest v hvK
      have hyx : y = x := highest_unique v z x y hr.1 hr.2
        (by
          rw [← huz]
          exact fun he => hne he.symm)
        (by
          intro t ht
          rw [← huz]
          exact (hag t ht).symm)
      rw [hyx]
      exact Finset.mem_insert_self x _
  · rcases Finset.mem_insert.mp hv with hvz | hvK
    · have hr := hrest u huK
      have hyx : y = x := highest_unique u z x y hr.1 hr.2
        (by
          rw [← hvz]
          exact hne)
        (by
          intro t ht
          rw [← hvz]
          exact hag t ht)
      rw [hyx]
      exact Finset.mem_insert_self x _
    · exact Finset.mem_insert_of_mem
        ((mem_levels K y).mpr ⟨u, huK, v, hvK, hne, hag⟩)

lemma levels_insert_sup {X : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)]
    (z : X → Bool) (K : Finset (X → Bool)) (x : X)
    (hrest : ∀ w ∈ K,
      w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hK : K.Nonempty) :
    insert x (levels K) ⊆ levels (insert z K) := by
  intro y hy
  rcases Finset.mem_insert.mp hy with hyx | hyK
  · obtain ⟨w, hw⟩ := hK
    rw [hyx]
    exact (mem_levels (insert z K) x).mpr
      ⟨w, Finset.mem_insert_of_mem hw,
       z, Finset.mem_insert_self z K,
       (hrest w hw).1, (hrest w hw).2⟩
  · exact levels_mono (Finset.subset_insert z K) hyK

lemma level_not_mem {X : Type*}
    [LinearOrder X] [Fintype X]
    (z : X → Bool) (K : Finset (X → Bool)) (x : X)
    (hrest : ∀ w ∈ K,
      w x ≠ z x ∧ ∀ y, x < y → w y = z y) :
    x ∉ levels K := by
  intro hx
  obtain ⟨u, hu, v, hv, hne, hag⟩ :=
    (mem_levels K x).mp hx
  exact hne (bool_other (u x) (z x) (v x)
    (hrest u hu).1 (hrest v hv).1)

lemma levels_insert_eq {X : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)]
    (z : X → Bool) (K : Finset (X → Bool)) (x : X)
    (hrest : ∀ w ∈ K,
      w x ≠ z x ∧ ∀ y, x < y → w y = z y)
    (hK : K.Nonempty) :
    levels (insert z K) = insert x (levels K) :=
  Finset.Subset.antisymm
    (levels_insert_sub z K x hrest)
    (levels_insert_sup z K x hrest hK)

lemma cat_card_levels {X : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool),
      K.card ≤ n → Cat K →
      K.card ≤ (levels K).card + 1 := by
  intro n
  induction n with
  | zero =>
      intro K hK hc
      omega
  | succ n ih =>
      intro K hKn hc
      by_cases hsmall : K.card ≤ 1
      · omega
      · obtain ⟨u, hu, v, hv, huv⟩ :=
          two_points K (by omega)
        obtain ⟨x, z, hz, hr, hne⟩ :=
          peel K hc u v hu hv huv
        have hsup := levels_insert_sup z (K.erase z) x hr hne
        rw [Finset.insert_erase hz] at hsup
        have hnot := level_not_mem z (K.erase z) x hr
        have h1 := Finset.card_erase_of_mem hz
        have h2 := Finset.card_le_card hsup
        rw [Finset.card_insert_of_notMem hnot] at h2
        have h3 := ih (K.erase z) (by omega)
          (cat_sub (Finset.erase_subset z K) hc)
        omega

lemma realize {X : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool),
      K.card ≤ n → Cat K → K.Nonempty →
      ∀ D : Finset X, D ⊆ levels K →
        ∃ A : Finset (X → Bool),
          A ⊆ K ∧ A.card = D.card + 1 ∧ levels A = D := by
  classical
  intro n
  induction n with
  | zero =>
      intro K hK hc hne D hD
      have hp := Finset.card_pos.mpr hne
      omega
  | succ n ih =>
      intro K hKn hc hne D hD
      by_cases hDe : D = ∅
      · obtain ⟨u, hu⟩ := hne
        refine ⟨{u}, Finset.singleton_subset_iff.mpr hu, ?_, ?_⟩
        · simp [hDe]
        · rw [hDe]
          exact levels_singleton u
      · obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr hDe
        obtain ⟨u, hu, v, hv, huv, hag⟩ :=
          (mem_levels K d).mp (hD hd)
        have hune : u ≠ v := by
          intro he
          exact huv (by rw [he])
        obtain ⟨x, z, hz, hr, hne'⟩ :=
          peel K hc u v hu hv hune
        have hcard : (K.erase z).card ≤ n := by
          have he := Finset.card_erase_of_mem hz
          omega
        have hc' : Cat (K.erase z) :=
          cat_sub (Finset.erase_subset z K) hc
        have hsub : levels K ⊆ insert x (levels (K.erase z)) := by
          have hh := levels_insert_sub z (K.erase z) x hr
          rw [Finset.insert_erase hz] at hh
          exact hh
        by_cases hxD : x ∈ D
        · have hD' : D.erase x ⊆ levels (K.erase z) := by
            intro y hy
            obtain ⟨hyx, hyD⟩ := Finset.mem_erase.mp hy
            rcases Finset.mem_insert.mp (hsub (hD hyD)) with he | he
            · exact (hyx he).elim
            · exact he
          obtain ⟨A, hA, hAc, hAd⟩ :=
            ih (K.erase z) hcard hc' hne' (D.erase x) hD'
          have hzA : z ∉ A :=
            fun hh => (Finset.mem_erase.mp (hA hh)).1 rfl
          have hAn : A.Nonempty :=
            Finset.card_pos.mp (by omega)
          refine ⟨insert z A,
            Finset.insert_subset hz
              (hA.trans (Finset.erase_subset z K)), ?_, ?_⟩
          · rw [Finset.card_insert_of_notMem hzA, hAc]
            have he := Finset.card_erase_of_mem hxD
            have hp := Finset.card_pos.mpr ⟨x, hxD⟩
            omega
          · rw [levels_insert_eq z A x
                (fun w hw => hr w (hA hw)) hAn, hAd]
            exact Finset.insert_erase hxD
        · have hD' : D ⊆ levels (K.erase z) := by
            intro y hy
            rcases Finset.mem_insert.mp (hsub (hD hy)) with he | he
            · exact (hxD (by rw [← he]; exact hy)).elim
            · exact he
          obtain ⟨A, hA, hAc, hAd⟩ :=
            ih (K.erase z) hcard hc' hne' D hD'
          exact ⟨A, hA.trans (Finset.erase_subset z K), hAc, hAd⟩

lemma color_cat {X C : Type*}
    [LinearOrder X] [Fintype X]
    (a : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hA : Cat A) :
    color a χ A = χ (levels A) := by
  classical
  unfold color
  rw [if_pos hA]

lemma color_noncat {X C : Type*}
    [LinearOrder X] [Fintype X]
    (a : C) (χ : Finset X → C)
    (A : Finset (X → Bool)) (hA : ¬ Cat A) :
    color a χ A = a := by
  classical
  unfold color
  rw [if_neg hA]

lemma homogeneous_cat_bound {X C : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)]
    (k s : ℕ) (a i : C) (χ : Finset X → C)
    (hχ : Solon.NoMono χ k s i)
    (K : Finset (X → Bool))
    (hm : ∀ A ⊆ K, A.card = k + 1 → color a χ A = i)
    (L : Finset (X → Bool)) (hLK : L ⊆ K) (hL : Cat L) :
    L.card ≤ s := by
  classical
  by_contra hbig
  have hc := cat_card_levels L.card L (le_refl _) hL
  obtain ⟨S, hS, hSc⟩ := Finset.exists_subset_card_eq
    (show s ≤ (levels L).card by omega)
  obtain ⟨D, hD, hne⟩ := hχ S hSc
  obtain ⟨hDS, hDc⟩ := Finset.mem_powersetCard.mp hD
  have hLn : L.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨A, hAL, hAc, hAd⟩ :=
    realize L.card L (le_refl _) hL hLn D (hDS.trans hS)
  have he := hm A (hAL.trans hLK) (by rw [hAc, hDc])
  rw [color_cat a χ A (cat_sub hAL hL), hAd] at he
  exact hne he

lemma cat_of_small_subsets {X : Type*}
    [LinearOrder X] [DecidableEq (X → Bool)]
    (k : ℕ) (hk : 3 ≤ k)
    (K : Finset (X → Bool)) (hK : k + 1 ≤ K.card)
    (hlocal : ∀ A ⊆ K, A.card = k + 1 → Cat A) :
    Cat K := by
  intro u hu v hv w hw z hz x huv hwz hag hbit hbit'
  have hSK : ({u, v, w, z} : Finset (X → Bool)) ⊆ K := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with he | he | he | he
    · rw [he]
      exact hu
    · rw [he]
      exact hv
    · rw [he]
      exact hw
    · rw [he]
      exact hz
  have hSc : ({u, v, w, z} : Finset (X → Bool)).card ≤ k + 1 := by
    have h1 := Finset.card_insert_le u
      ({v, w, z} : Finset (X → Bool))
    have h2 := Finset.card_insert_le v
      ({w, z} : Finset (X → Bool))
    have h3 := Finset.card_insert_le w
      ({z} : Finset (X → Bool))
    rw [Finset.card_singleton] at h3
    omega
  obtain ⟨A, hSA, hAK, hAc⟩ :=
    extend ({u, v, w, z} : Finset (X → Bool))
      K (k + 1) hSK hSc hK
  exact (hlocal A hAK hAc)
    u (hSA (by simp))
    v (hSA (by simp))
    w (hSA (by simp))
    z (hSA (by simp))
    x huv hwz hag hbit hbit'

lemma large_cat {X : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)] :
    ∀ n : ℕ, ∀ K : Finset (X → Bool),
      2 ^ n < K.card →
      ∃ L : Finset (X → Bool),
        L ⊆ K ∧ Cat L ∧ n + 2 ≤ L.card := by
  classical
  intro n
  induction n with
  | zero =>
      intro K hK
      have htwo : 2 ≤ K.card := by
        simp only [pow_zero] at hK
        omega
      obtain ⟨u, hu, v, hv, huv⟩ := two_points K htwo
      refine ⟨{u, v}, ?_, cat_pair u v, ?_⟩
      · exact Finset.insert_subset hu
          (Finset.singleton_subset_iff.mpr hv)
      · rw [Finset.card_pair huv]
  | succ n ih =>
      intro K hK
      have hp : 0 < (2 : ℕ) ^ (n + 1) :=
        pow_pos (by decide) (n + 1)
      obtain ⟨u, hu, v, hv, huv⟩ :=
        two_points K (by omega)
      obtain ⟨x, hag, r, hr, t, ht, hrt⟩ :=
        top K u v hu hv huv
      have hop : ∃ p ∈ K, p x = false ∧
          ∃ q ∈ K, q x = true := by
        rcases bool_different (r x) (t x) hrt with hh | hh
        · exact ⟨r, hr, hh.1, t, ht, hh.2⟩
        · exact ⟨t, ht, hh.2, r, hr, hh.1⟩
      obtain ⟨p, hpK, hpf, q, hqK, hqt⟩ := hop
      let P : Finset (X → Bool) :=
        K.filter (fun w => w x = false)
      let Q : Finset (X → Bool) :=
        K.filter (fun w => w x = true)
      have hPK : P ⊆ K := Finset.filter_subset _ _
      have hQK : Q ⊆ K := Finset.filter_subset _ _
      have hPbit : ∀ w ∈ P, w x = false := by
        intro w hw
        exact (Finset.mem_filter.mp hw).2
      have hQbit : ∀ w ∈ Q, w x = true := by
        intro w hw
        exact (Finset.mem_filter.mp hw).2
      have hd : Disjoint P Q := by
        rw [Finset.disjoint_left]
        intro w hwP hwQ
        have he : false = true :=
          (hPbit w hwP).symm.trans (hQbit w hwQ)
        exact (by decide : ¬ (false = true)) he
      have hcover : P ∪ Q = K := by
        ext w
        simp only [P, Q, Finset.mem_union, Finset.mem_filter]
        cases he : w x <;> simp [he]
      have hsum : P.card + Q.card = K.card := by
        rw [← Finset.card_union_of_disjoint hd, hcover]
      have hpow : (2 : ℕ) ^ (n + 1) = 2 ^ n + 2 ^ n := by
        rw [pow_succ]
        omega
      have make :
          ∀ M : Finset (X → Bool), M ⊆ K →
          ∀ z ∈ K, (∀ w ∈ M, w x ≠ z x) →
          2 ^ n < M.card →
          ∃ L : Finset (X → Bool),
            L ⊆ K ∧ Cat L ∧ n + 1 + 2 ≤ L.card := by
        intro M hMK z hz hcross hbig
        obtain ⟨L, hLM, hLc, hLcard⟩ := ih M hbig
        have hrest : ∀ w ∈ L,
            w x ≠ z x ∧ ∀ y, x < y → w y = z y := by
          intro w hw
          exact ⟨hcross w (hLM hw),
            fun y hy => hag w (hMK (hLM hw)) z hz y hy⟩
        have hzL : z ∉ L := fun hh => (hrest z hh).1 rfl
        refine ⟨insert z L,
          Finset.insert_subset hz (hLM.trans hMK),
          cat_insert z L x hrest hLc, ?_⟩
        rw [Finset.card_insert_of_notMem hzL]
        omega
      by_cases hPbig : 2 ^ n < P.card
      · apply make P hPK q hqK
        · intro w hw he
          have hf : false = true :=
            (hPbit w hw).symm.trans (he.trans hqt)
          exact (by decide : ¬ (false = true)) hf
        · exact hPbig
      · apply make Q hQK p hpK
        · intro w hw he
          have hf : true = false :=
            (hQbit w hw).symm.trans (he.trans hpf)
          exact (by decide : ¬ (true = false)) hf
        · omega

lemma other_noMono {X C : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)]
    (k s : ℕ) (hk : 3 ≤ k) (hs : k ≤ s)
    (a i : C) (hia : i ≠ a) (χ : Finset X → C)
    (hχ : Solon.NoMono χ k s i) :
    Solon.NoMono (color a χ) (k + 1) (s + 1) i := by
  classical
  intro K hK
  by_contra hn
  have hm : ∀ A ⊆ K, A.card = k + 1 → color a χ A = i := by
    intro A hAK hAc
    by_contra hne
    exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hAK, hAc⟩, hne⟩
  have hlocal : ∀ A ⊆ K, A.card = k + 1 → Cat A := by
    intro A hAK hAc
    by_contra hnc
    have he := hm A hAK hAc
    rw [color_noncat a χ A hnc] at he
    exact hia he.symm
  have hc : Cat K :=
    cat_of_small_subsets k hk K (by omega) hlocal
  have hb := homogeneous_cat_bound k s a i χ hχ
    K hm K (fun _ h => h) hc
  omega

lemma fallback_noMono {X C : Type*}
    [LinearOrder X] [Fintype X] [DecidableEq (X → Bool)]
    (k s : ℕ) (hs : 1 ≤ s)
    (a : C) (χ : Finset X → C)
    (hχ : Solon.NoMono χ k s a) :
    Solon.NoMono (color a χ) (k + 1) (2 ^ (s - 1) + 1) a := by
  classical
  intro K hK
  by_contra hn
  have hm : ∀ A ⊆ K, A.card = k + 1 → color a χ A = a := by
    intro A hAK hAc
    by_contra hne
    exact hn ⟨A, Finset.mem_powersetCard.mpr ⟨hAK, hAc⟩, hne⟩
  obtain ⟨L, hLK, hLc, hLcard⟩ :=
    large_cat (s - 1) K (by omega)
  have hb := homogeneous_cat_bound k s a a χ hχ
    K hm L hLK hLc
  omega

end FallbackStep

theorem stepping_up_one_fallback_all_palettes :
    ∀ {X C : Type*} [LinearOrder X] [Fintype X] [DecidableEq C]
      (k : ℕ), 3 ≤ k →
      ∀ (a : C) (s : C → ℕ), (∀ i, k ≤ s i) →
      ∀ χ : Finset X → C,
        (∀ i, Solon.NoMono χ k (s i) i) →
        ∃ ψ : Finset (X → Bool) → C,
          ∀ i, Solon.NoMono ψ (k + 1)
            (oneFallbackStepSize a s i) i := by
  intro X C _ _ _ k hk a s hs χ hχ
  classical
  refine ⟨FallbackStep.color a χ, ?_⟩
  intro i
  by_cases hi : i = a
  · subst i
    have hh := FallbackStep.fallback_noMono k (s a)
      (by have h := hs a; omega) a χ (hχ a)
    simpa [oneFallbackStepSize] using hh
  · have hh := FallbackStep.other_noMono k (s i)
      hk (hs i) a i hi χ (hχ i)
    simpa [oneFallbackStepSize, hi] using hh

