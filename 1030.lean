import Mathlib
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of Ramsey number R(k, l) as the smallest n such that every graph on n vertices has a k-clique or an l-independent set.
-/
open SimpleGraph Filter Topology

/-- `IsRamsey n k l` means that every graph on `n` vertices has a clique of size `k`
or an independent set of size `l`. -/
def IsRamsey (n k l : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)), (∃ s, G.IsNClique k s) ∨ (∃ t, G.IsNIndepSet l t)

/-- The Ramsey number `R(k, l)` is the smallest `n` such that `IsRamsey n k l` holds. -/
noncomputable def R (k l : ℕ) : ℕ :=
  sInf {n | IsRamsey n k l}

/-
Ramsey's theorem: for any k, l ≥ 1, there exists an n such that any graph on n vertices has a k-clique or an l-independent set.
-/
theorem R_well_defined (k l : ℕ) (hk : k ≥ 1) (hl : l ≥ 1) : ∃ n, IsRamsey n k l := by
  -- We proceed by induction on $k + l$.
  induction' k using Nat.strong_induction_on with k ih generalizing l;
  induction' l using Nat.strong_induction_on with l ih';
  rcases k with ( _ | _ | k ) <;> rcases l with ( _ | _ | l ) <;> simp_all +decide;
  · -- For the base case when $k = 1$ and $l = 1$, any graph on $n$ vertices will have a 1-clique (any single vertex) and a 1-independent set (any single vertex). Thus, $n = 1$ works.
    use 1
    simp [IsRamsey];
  · -- For the base case when $k = 1$, any graph on $n$ vertices trivially has a $1$-clique (since any vertex is a $1$-clique).
    use 1
    intro G
    simp [IsRamsey];
  · use k + 2;
    intro G;
    exact Or.inr ⟨ { ⟨ 0, by linarith ⟩ }, by simp +decide [ SimpleGraph.isNIndepSet_iff ] ⟩;
  · -- Let $n = n_1 + n_2$.
    obtain ⟨n₁, hn₁⟩ := ih (k + 1) (by linarith) (l + 2) (by linarith) (by linarith)
    obtain ⟨n₂, hn₂⟩ := ih' (l + 1) (by linarith) (by linarith);
    use n₁ + n₂ + 1;
    -- Consider any graph $G$ on $n₁ + n₂ + 1$ vertices. Pick a vertex $v$. Let $S$ be the neighbors of $v$ and $T$ be the non-neighbors.
    intro G
    obtain ⟨v, hv⟩ : ∃ v : Fin (n₁ + n₂ + 1), True := by
      exact ⟨ 0, trivial ⟩;
    -- Let $S$ be the set of neighbors of $v$ and $T$ be the set of non-neighbors of $v$.
    set S := Finset.filter (fun u => G.Adj v u) (Finset.univ.erase v)
    set T := Finset.filter (fun u => ¬G.Adj v u) (Finset.univ.erase v);
    -- Since $|S| + |T| = n₁ + n₂$, either $|S| \geq n₁$ or $|T| \geq n₂$.
    by_cases hS : S.card ≥ n₁;
    · -- By the induction hypothesis, $G[S]$ has a $(k+1)$-clique or an $(l+2)$-independent set.
      obtain ⟨s, hs⟩ : ∃ s : Finset (Fin (n₁ + n₂ + 1)), s ⊆ S ∧ (G.IsNClique (k + 1) s ∨ G.IsNIndepSet (l + 2) s) := by
        have := hn₁;
        -- Since $|S| \geq n₁$, we can map the vertices of $S$ to a subset of $\{0, 1, ..., n₁ - 1\}$.
        obtain ⟨f, hf⟩ : ∃ f : Fin n₁ → Fin (n₁ + n₂ + 1), Function.Injective f ∧ ∀ i, f i ∈ S := by
          have := Finset.exists_subset_card_eq hS;
          obtain ⟨ t, ht₁, ht₂ ⟩ := this;
          exact ⟨ fun i => t.orderEmbOfFin ( by aesop ) i, by aesop_cat, fun i => ht₁ <| by aesop ⟩;
        specialize this ( SimpleGraph.comap f G );
        rcases this with ( ⟨ s, hs ⟩ | ⟨ t, ht ⟩ );
        · use Finset.image f s;
          simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff ];
          simp_all +decide [ SimpleGraph.isClique_iff, Finset.card_image_of_injective _ hf.1 ];
          exact Or.inl fun x hx y hy hxy => by obtain ⟨ i, hi, rfl ⟩ := hx; obtain ⟨ j, hj, rfl ⟩ := hy; exact hs.1 hi hj ( by aesop ) ;
        · use Finset.image f t;
          simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff ];
          simp_all +decide [ SimpleGraph.isIndepSet_iff, Finset.card_image_of_injective _ hf.1 ];
          simp_all +decide [ Set.Pairwise, Finset.mem_image ];
          exact Or.inr fun a ha b hb hab => ht.1 ha hb ( by contrapose! hab; aesop );
      aesop;
      · refine Or.inl ⟨ Insert.insert v s, ?_ ⟩;
        simp_all +decide [ SimpleGraph.isNClique_iff ];
        exact ⟨ fun u hu hu' => by have := left hu; aesop, by rw [ Finset.card_insert_of_notMem ( fun hu => by have := left hu; aesop ), h.2 ] ⟩;
      · exact Or.inr ⟨ s, h_1 ⟩;
    · -- Since $|T| \geq n₂$, by the induction hypothesis, $G[T]$ has a $(k+2)$-clique or an $(l+1)$-independent set.
      obtain ⟨t, ht⟩ : ∃ t : Finset (Fin (n₁ + n₂ + 1)), t ⊆ T ∧ (G.IsNClique (k + 2) t ∨ G.IsNIndepSet (l + 1) t) := by
        have hT : T.card ≥ n₂ := by
          have hT : S.card + T.card = n₁ + n₂ := by
            rw [ Finset.filter_card_add_filter_neg_card_eq_card ] ; aesop;
          linarith;
        -- Since $T$ has at least $n₂$ elements, and by the induction hypothesis, any graph on $n₂$ vertices has a $(k+2)$-clique or an $(l+1)$-independent set, we can apply the induction hypothesis to the subgraph induced by $T$.
        have h_ind : ∀ (G : SimpleGraph (Fin n₂)), (∃ t : Finset (Fin n₂), G.IsNClique (k + 2) t ∨ G.IsNIndepSet (l + 1) t) := by
          exact fun G => by have := hn₂ G; aesop;
        -- Let $f : Fin n₂ → T$ be an injective function.
        obtain ⟨f, hf_inj⟩ : ∃ f : Fin n₂ → Fin (n₁ + n₂ + 1), Function.Injective f ∧ ∀ i, f i ∈ T := by
          have := Finset.exists_subset_card_eq hT;
          obtain ⟨ t, ht₁, ht₂ ⟩ := this; exact ⟨ fun i => t.orderEmbOfFin ( by aesop ) i, by aesop_cat, fun i => ht₁ <| by aesop ⟩ ;
        obtain ⟨ t, ht ⟩ := h_ind ( SimpleGraph.comap f G );
        use Finset.image f t;
        simp_all +decide [ Finset.subset_iff, SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff ];
        simp_all +decide [ SimpleGraph.IsClique, SimpleGraph.IsIndepSet, Finset.card_image_of_injective _ hf_inj.1 ];
        simp_all +decide [ Set.Pairwise, Function.Injective.eq_iff hf_inj.1 ];
      aesop;
      · exact Or.inl ⟨ t, h ⟩;
      · refine Or.inr ⟨ Insert.insert v t, ?_ ⟩;
        simp_all +decide [ SimpleGraph.isNIndepSet_iff, Finset.subset_iff ];
        simp_all +decide [ Set.Pairwise, Finset.card_insert_of_notMem ];
        exact ⟨ fun x hx => by simpa [ SimpleGraph.adj_comm ] using left hx |>.2, by rw [ Finset.card_insert_of_notMem ( fun hx => by simpa [ left hx ] using left hx |>.1 ), h_1.2 ] ⟩

/-
Definition of the join of two graphs.
-/
/-- The join of two graphs `G` and `H` is the graph on `α ⊕ β` where vertices in `G` are adjacent
to vertices in `H`, and edges within `G` and `H` are preserved. -/
def SimpleGraph.join {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α ⊕ β) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
  symm := by
    -- To prove symmetry, we need to show that if x is adjacent to y, then y is adjacent to x.
    intros x y hxy
    cases x <;> cases y <;> simp_all +decide [ Symmetric ];
    · exact hxy.symm;
    · -- Since adjacency is symmetric in a simple graph, if H.Adj a b, then H.Adj b a.
      apply hxy.symm
  loopless := by
    -- To prove irreflexivity, we need to show that for any vertex x, x is not adjacent to itself.
    intro x
    cases x <;> simp [SimpleGraph.Adj]

infixl:60 " ⊕j " => SimpleGraph.join

/-
Checking types of Finset.preimage and Function.Injective.injOn
-/
#check Finset.preimage
#check Function.Injective.injOn

/-
Characterization of cliques in the join of two graphs.
-/
theorem join_clique_iff {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) (s : Finset (α ⊕ β)) :
    (G ⊕j H).IsClique s ↔ (G.IsClique (s.preimage Sum.inl Sum.inl_injective.injOn)) ∧
                           (H.IsClique (s.preimage Sum.inr Sum.inr_injective.injOn)) := by
  simp +decide [ Set.Pairwise, SimpleGraph.join ]

/-
Characterization of independent sets in the join of two graphs.
-/
theorem join_indep_iff {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) (s : Finset (α ⊕ β)) :
    (G ⊕j H).IsIndepSet s ↔ (s.preimage Sum.inr Sum.inr_injective.injOn = ∅ ∧ G.IsIndepSet (s.preimage Sum.inl Sum.inl_injective.injOn)) ∨
                             (s.preimage Sum.inl Sum.inl_injective.injOn = ∅ ∧ H.IsIndepSet (s.preimage Sum.inr Sum.inr_injective.injOn)) := by
  constructor;
  · -- If $s$ is an independent set in the join of $G$ and $H$, then for any $u \in s$, if $u$ is in $G$, then all other vertices in $s$ must also be in $G$ because otherwise, there would be an edge between $u$ and a vertex in $H$. Similarly, if $u$ is in $H$, then all other vertices must be in $H$.
    intro hs
    by_cases hG : ∃ u ∈ s, u ∈ Set.range Sum.inl;
    · obtain ⟨ u, hu₁, ⟨ v, rfl ⟩ ⟩ := hG;
      refine' Or.inl ⟨ Finset.eq_empty_of_forall_notMem fun x hx => _, _ ⟩;
      · have := hs hu₁ ( Finset.mem_preimage.mp hx ) ; simp_all +decide [ SimpleGraph.join ] ;
      · -- Since $s$ is an independent set in the join of $G$ and $H$, any two elements in $s$ that are in $G$ must not be adjacent. Therefore, the preimage of $s$ under $Sum.inl$ is an independent set in $G$.
        intros u hu v hv huv;
        have := hs ( Finset.mem_preimage.mp hu ) ( Finset.mem_preimage.mp hv ) ; aesop;
    · refine' Or.inr ⟨ _, _ ⟩;
      · aesop;
      · intro x hx y hy hxy; have := hs ( Finset.mem_preimage.mp hx ) ( Finset.mem_preimage.mp hy ) ; aesop;
  · bound;
    · simp_all +decide [ SimpleGraph.IsIndepSet, Finset.ext_iff ];
      intro x hx y hy hxy; cases x <;> cases y <;> simp_all +decide [ SimpleGraph.join ] ;
      exact right ( by aesop ) ( by aesop ) hxy;
    · simp_all +decide [ Finset.ext_iff, Set.insert_subset_iff ];
      intro x hx y hy hxy; cases x <;> cases y <;> aesop;

/-
R(k, l) is the smallest number satisfying the Ramsey property.
-/
theorem R_spec (k l : ℕ) (hk : k ≥ 1) (hl : l ≥ 1) : IsRamsey (R k l) k l ∧ ∀ n < R k l, ¬ IsRamsey n k l := by
  have h : {n | IsRamsey n k l}.Nonempty := R_well_defined k l hk hl
  constructor
  · exact Nat.sInf_mem h
  · intro n hn
    exact Nat.not_mem_of_lt_sInf hn

/-
If there is a counterexample graph on a type with n elements, then IsRamsey n k l is false.
-/
lemma not_isRamsey_of_counterexample {n k l : ℕ} {α : Type*} [Fintype α] (h_card : Fintype.card α = n)
    (G : SimpleGraph α) (h_clique : ∀ s, ¬ G.IsNClique k s) (h_indep : ∀ t, ¬ G.IsNIndepSet l t) :
    ¬ IsRamsey n k l := by
      -- By definition of IsRamsey, if there exists a graph G on n vertices with no k-clique and no l-independent set, then IsRamsey n k l is false.
      simp [IsRamsey];
      have h_iso : Nonempty (α ≃ Fin n) := by
        exact ⟨ Fintype.equivFinOfCardEq h_card ⟩;
      obtain ⟨ e ⟩ := h_iso;
      refine' ⟨ _, _, _ ⟩;
      exact SimpleGraph.comap e.symm G;
      · intro s hs;
        refine' h_clique ( Finset.image ( fun x => e.symm x ) s ) _;
        simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective _ e.symm.injective ];
        exact fun x hx y hy hxy => by obtain ⟨ u, hu, rfl ⟩ := hx; obtain ⟨ v, hv, rfl ⟩ := hy; exact hs.1 hu hv ( by aesop ) ;
      · intro s hs; specialize h_indep ( Finset.image ( fun x : Fin n => e.symm x ) s ) ; simp_all +decide [ SimpleGraph.isNClique_iff, SimpleGraph.isNIndepSet_iff ] ;
        simp_all +decide [ SimpleGraph.IsIndepSet, Finset.card_image_of_injective _ e.symm.injective ];
        simp_all +decide [ Set.Pairwise ];
        obtain ⟨ x, hx, y, hy, hxy, h ⟩ := h_indep; have := hs.1 hx hy; simp_all +decide [ SimpleGraph.adj_comm ] ;

/-
Lower bound for R(k+1, k).
-/
theorem R_ge_add_k_sub_one (k : ℕ) (hk : 2 ≤ k) : R (k + 1) k ≥ R k k + k - 1 := by
  -- Let's construct the graph $G$ as the join of $G_1$ and $G_2$.
  obtain ⟨G1, hG1⟩ : ∃ G1 : SimpleGraph (Fin (R k k - 1)), (∀ s : Finset (Fin (R k k - 1)), ¬ G1.IsNClique k s) ∧ (∀ t : Finset (Fin (R k k - 1)), ¬ G1.IsNIndepSet k t) := by
    -- By definition of $R$, we know that $R(k, k) - 1$ is not sufficient to guarantee a $k$-clique or $k$-independent set.
    have h_not_suff : ¬IsRamsey (R k k - 1) k k := by
      -- By definition of $R$, we know that $R(k, k)$ is the smallest number such that every graph on $n$ vertices has a $k$-clique or a $k$-independent set.
      have h_def : IsRamsey (R k k) k k ∧ ∀ n < R k k, ¬ IsRamsey n k k := by
        exact R_spec k k ( by linarith ) ( by linarith );
      rcases n : R k k with ( _ | _ | n ) <;> aesop;
      specialize h_def ⊥ ; aesop;
      · linarith;
      · rcases k with ( _ | _ | k ) <;> simp_all +decide [ SimpleGraph.isNIndepSet_iff ];
        fin_cases w ; aesop;
    contrapose! h_not_suff;
    exact fun G => Classical.or_iff_not_imp_left.2 fun h => by push_neg at h; aesop;
  -- Let's construct the graph $G$ as the join of $G_1$ and $G_2$ and show that it has no $(k+1)$-clique or $k$-independent set.
  obtain ⟨G, hG⟩ : ∃ G : SimpleGraph (Fin (R k k - 1 + (k - 1))), (∀ s : Finset (Fin (R k k - 1 + (k - 1))), ¬ G.IsNClique (k + 1) s) ∧ (∀ t : Finset (Fin (R k k - 1 + (k - 1))), ¬ G.IsNIndepSet k t) := by
    -- Let's construct the graph $G$ as the join of $G_1$ and $G_2$ and show that it has no $(k+1)$-clique or $k$-independent set. We'll use the fact that $G_1$ has no $k$-clique and no $k$-independent set.
    have h_join : ∃ G : SimpleGraph (Fin (R k k - 1) ⊕ Fin (k - 1)), (∀ s : Finset (Fin (R k k - 1) ⊕ Fin (k - 1)), ¬ G.IsNClique (k + 1) s) ∧ (∀ t : Finset (Fin (R k k - 1) ⊕ Fin (k - 1)), ¬ G.IsNIndepSet k t) := by
      refine' ⟨ SimpleGraph.join G1 ⊥, _, _ ⟩;
      · -- Any clique in the join must be a subset of the vertices of G1 or the empty graph. Since the empty graph has no edges, any clique in the join can't have more than one vertex from the empty graph. Therefore, the size of the clique is bounded by the size of the largest clique in G1 plus one.
        intros s hs
        have h_clique : s.card ≤ (s.preimage Sum.inl Sum.inl_injective.injOn).card + 1 := by
          have h_clique : s.card ≤ (s.preimage Sum.inl Sum.inl_injective.injOn).card + (s.preimage Sum.inr Sum.inr_injective.injOn).card := by
            rw [ Finset.card_preimage, Finset.card_preimage ];
            rw [ ← Finset.card_union_add_card_inter ];
            exact le_add_right ( Finset.card_le_card fun x hx => by cases x <;> aesop );
          have h_clique : (s.preimage Sum.inr Sum.inr_injective.injOn).card ≤ 1 := by
            exact Finset.card_le_one.mpr fun x hx y hy => Classical.not_not.1 fun hxy => by have := hs.1 ( Finset.mem_preimage.mp hx ) ( Finset.mem_preimage.mp hy ) ; aesop;
          linarith;
        -- Since $s$ is a clique in the join, its preimage under $Sum.inl$ must be a clique in $G1$.
        have h_clique_G1 : (s.preimage Sum.inl Sum.inl_injective.injOn).card ≤ k - 1 := by
          have h_clique_G1 : ∀ s : Finset (Fin (R k k - 1)), G1.IsClique s → s.card ≤ k - 1 := by
            intro s hs; contrapose! hG1; aesop;
            -- Since $s$ is a clique in $G1$ and $s.card \geq k$, we can extract a $k$-clique from $s$.
            obtain ⟨t, ht⟩ : ∃ t : Finset (Fin (R k k - 1)), t ⊆ s ∧ t.card = k ∧ G1.IsClique t := by
              obtain ⟨ t, ht ⟩ := Finset.exists_subset_card_eq ( show k ≤ s.card from by omega ) ; use t; aesop;
              exact fun x hx y hy hxy => hs ( left hx ) ( left hy ) hxy;
            exact False.elim <| ‹∀ s : Finset ( Fin ( R k k - 1 ) ), ¬G1.IsNClique k s› t <| by rw [ SimpleGraph.isNClique_iff ] ; aesop;
          convert h_clique_G1 _ _;
          intro x hx y hy; have := hs.1; aesop;
          have := this hx hy; aesop;
        have := hs.2; simp_all +decide [ SimpleGraph.IsNClique ] ;
        omega;
      · intro t ht;
        -- Since $t$ is an independent set in the join of $G1$ and the empty graph, it must be entirely contained in either $G1$ or the empty graph.
        by_cases h_cases : t ⊆ Finset.image (Sum.inl) (Finset.univ : Finset (Fin (R k k - 1))) ∨ t ⊆ Finset.image (Sum.inr) (Finset.univ : Finset (Fin (k - 1)));
        · cases' h_cases with h_cases h_cases;
          · -- Since $t$ is an independent set in the join of $G1$ and the empty graph, it must be entirely contained in $G1$.
            obtain ⟨s, hs⟩ : ∃ s : Finset (Fin (R k k - 1)), t = Finset.image (Sum.inl) s := by
              use Finset.filter (fun x => Sum.inl x ∈ t) Finset.univ;
              ext x; have := @h_cases x; aesop;
            simp_all +decide [ SimpleGraph.isNIndepSet_iff ];
            simp_all +decide [ SimpleGraph.IsIndepSet, Finset.card_image_of_injective, Function.Injective ];
            exact hG1.2 s ( by simpa [ Set.Pairwise ] using ht.1 ) ht.2;
          · have := Finset.card_le_card h_cases; simp_all +decide [ Finset.card_image_of_injective, Function.Injective ] ;
            exact absurd this ( by have := ht.2; omega );
        · simp_all +decide [ Finset.subset_iff ];
          obtain ⟨ ⟨ x, hx ⟩, ⟨ y, hy ⟩ ⟩ := h_cases;
          have := ht.1 hx hy; simp_all +decide [ SimpleGraph.join ] ;
    obtain ⟨ G, hG₁, hG₂ ⟩ := h_join;
    -- Let's construct the graph $G$ on $Fin (R k k - 1 + (k - 1))$ by mapping the vertices of $G$ to $Fin (R k k - 1 + (k - 1))$.
    obtain ⟨f, hf⟩ : ∃ f : Fin (R k k - 1 + (k - 1)) ≃ Fin (R k k - 1) ⊕ Fin (k - 1), True := by
      exact ⟨ Fintype.equivOfCardEq <| by simp +decide, trivial ⟩;
    refine' ⟨ G.comap f, _, _ ⟩ <;> simp_all +decide [ SimpleGraph.comap, SimpleGraph.IsNClique, SimpleGraph.IsNIndepSet ];
    · intro s hs; specialize hG₁ ( Finset.image f s ) ; simp_all +decide [ SimpleGraph.isNClique_iff ] ;
      simp_all +decide [ Finset.card_image_of_injective _ f.injective, SimpleGraph.IsClique ];
      contrapose! hG₁; simp_all +decide [ Set.Pairwise ] ;
      constructor <;> intro a ha <;> constructor <;> intro b hb <;> have := hs.1 ha hb <;> aesop;
    · intro t ht; specialize hG₂ ( t.image f ) ; simp_all +decide [ SimpleGraph.isNIndepSet_iff ] ;
      simp_all +decide [ SimpleGraph.IsIndepSet, Finset.card_image_of_injective _ f.injective ];
      contrapose! hG₂; simp_all +decide [ Set.Pairwise ] ;
      constructor <;> intro a ha <;> constructor <;> intro b hb <;> have := ht.1 ha hb <;> simp_all +decide [ Equiv.symm_apply_eq ] ;
  -- Therefore, $R(k+1, k) > R(k, k) + k - 2$.
  have h_R_gt : ¬IsRamsey (R k k - 1 + (k - 1)) (k + 1) k := by
    exact fun h => by rcases h G with h|h <;> tauto;
  have h_R_ge : R (k + 1) k > R k k - 1 + (k - 1) := by
    contrapose! h_R_gt;
    have := R_spec ( k + 1 ) k ( by linarith ) ( by linarith );
    refine' fun G => _;
    have := this.1 ( G.comap ( Fin.castLE h_R_gt ) );
    rcases this with ( ⟨ s, hs ⟩ | ⟨ t, ht ⟩ );
    · refine' Or.inl ⟨ s.image ( Fin.castLE h_R_gt ), _ ⟩;
      simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective, Function.Injective ];
      intro x hx y hy; aesop;
    · refine Or.inr ⟨ Finset.image ( Fin.castLE h_R_gt ) t, ?_ ⟩;
      simp_all +decide [ SimpleGraph.isNIndepSet_iff, Finset.card_image_of_injective, Function.Injective ];
      simp_all +decide [ SimpleGraph.IsIndepSet, Set.Pairwise ];
  omega

/-
R(k, k) is at least 1 for k >= 1.
-/
lemma R_ge_one (k : ℕ) (hk : k ≥ 1) : R k k ≥ 1 := by
  have := @R_spec k k hk hk;
  contrapose! this; aesop;
  specialize ‹IsRamsey 0 k k› ⊥ ; aesop;
  · exact hk.ne_empty ( Finset.eq_empty_of_forall_notMem fun x hx => by fin_cases x );
  · -- The only graph on 0 vertices is the empty graph, which cannot have a clique or independent set of size k when k ≥ 1.
    have h_empty : ∀ (G : SimpleGraph (Fin 0)), ¬(∃ s : Finset (Fin 0), G.IsNClique k s) ∧ ¬(∃ t : Finset (Fin 0), G.IsNIndepSet k t) := by
      simp +zetaDelta at *;
      intro G; constructor <;> intro x <;> fin_cases x <;> aesop;
      cases a ; aesop;
    exact h_empty _ |>.2 ⟨ w, h ⟩

/-
The ratio R(k+1, k) / R(k, k) is eventually at least 1.
-/
lemma ratio_ge_one_eventually : ∀ᶠ k in Filter.atTop, 1 ≤ (R (k+1) k : ℝ) / R k k := by
  -- By combining the results from R_ge_add_k_sub_one and R_ge_one, we can conclude that for k ≥ 2, the ratio R(k+1, k) / R(k, k) is at least 1.
  have h_ratio : ∀ k ≥ 2, 1 ≤ (R (k + 1) k : ℝ) / (R k k : ℝ) := by
    -- For any $k \geq 2$, we know from the provided solution that $R(k+1, k) \geq R(k, k)$.
    intros k hk
    have h_ge : (R (k + 1) k : ℝ) ≥ (R k k : ℝ) := by
      have h_ge : R (k + 1) k ≥ R k k + k - 1 := by
        exact?;
      exact_mod_cast le_trans ( Nat.le_sub_one_of_lt ( Nat.lt_add_of_pos_right ( pos_of_gt hk ) ) ) h_ge;
    rw [ one_le_div ] <;> norm_cast at * ; linarith [ R_ge_one k ( by linarith ) ];
  exact Filter.eventually_atTop.mpr ⟨ 2, h_ratio ⟩

/-
Checking the type of Filter.liminf_le_liminf_of_le
-/
#check Filter.liminf_le_liminf_of_le
