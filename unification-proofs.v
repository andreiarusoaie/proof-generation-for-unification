(* 
The purpose of this file is to check some proofs presented in a research paper 
on unification in the context of Matching Logic.

The contents of this file:
1. The syntax of Matching Logic formulae (patterns): line 25
2. Substitution function and helper lemmas : line 73
3. Axiomatisation of Definedness, Totality, Membership, Equality: line 54
4. Axioms and rules of a sub-proof system of Matching Logic: line 152
5. Helper lemmas and theorems, intermediate results: line 194
6. The main paper proofs: line 659
*)


Require Import String.
Require Import List.
Require Import ZArith.
Import ListNotations.

Definition sort := string.
Inductive Symbol := symb : string -> list sort -> sort -> Symbol. 
Variable s₁ : sort.
Variable s₂ : sort.

(* ML Pattern syntax *)
Inductive Pattern :=
| var : string -> Pattern
| symbol : Symbol -> list Pattern -> Pattern
| not : Pattern -> Pattern
| and : Pattern -> Pattern -> Pattern
| Exists : string -> Pattern -> Pattern.

Notation "¬ A" := (not A) (at level 80).
Notation "A ∧ B" := (and A B) (at level 81).

(* Other (allowed) syntactical connectives in ML are axiomatised. *)
Parameter or : Pattern -> Pattern -> Pattern.
Notation "A ∨ B" := (or A B) (at level 82).
Axiom or_and : forall A B, (A ∧ B) = ¬ (¬ A ∨ ¬ B).

Parameter implies : Pattern -> Pattern -> Pattern.
Notation "A → B" := (implies A B) (at level 84).
Axiom implies_or : forall A B, (A → B) = ¬ A ∨ B.

Parameter equiv : Pattern -> Pattern -> Pattern.
Notation "A ↔ B" := (equiv A B) (at level 83).
Axiom equivalence : forall A B, (A ↔ B) = ((A → B) ∧ (B → A)).

Parameter Top : Pattern.
Notation "⊤" := (Top).



(* Definedness, Totality, Membership, Equality are also axiomatised. *)
(* These axioms are in fact trivial lemma in our term pattern setting. *)
Parameter definedness : Pattern -> sort -> sort -> Pattern.
Notation "⌈ A ⌉ " := (definedness A s₁ s₂) (at level 90).

Definition totality (φ : Pattern) (s₁ s₂ : string) : Pattern :=  ¬ ⌈ ¬ φ ⌉.
Notation "⌊ A ⌋ " := (totality A s₁ s₂) (at level 90).

Definition equal (φ φ' : Pattern) : Pattern := ⌊ φ ↔ φ' ⌋.
Notation "A == B" := (equal A B) (at level 80).
Axiom equal_symmetry: forall A B, (A == B) = (B == A).
Axiom equal_equiv: forall φ φ', (φ ↔ φ') = (φ == φ').

Definition membership (φ φ' : Pattern) : Pattern := ⌈ φ ∧ φ' ⌉.
Notation "A ∈ B" := (membership A B) (at level 80).
Lemma membership_helper: forall A B, (⌈ A ∧ B ⌉) = (A ∈ B).
Proof. intros. unfold membership. reflexivity. Qed.


(* Substitution functions and helpers. *)
Fixpoint substitution' (h : nat) (φ' : Pattern) (x : string) (φ : Pattern) : Pattern :=
  match h with
  | O => φ
  | S m => match φ with
           | var y => if (string_dec x y) then φ' else φ
           | symbol σ args => (symbol σ (map (substitution' m  φ' x) args))
           | not ψ => not (substitution' m φ' x ψ)
           | and ψ ψ' => and (substitution' m  φ' x ψ) (substitution' m φ' x ψ')
           | Exists y ψ => if (string_dec x y)
                           then Exists y ψ
                           else Exists y (substitution' m φ' x ψ)
           end
  end.

Lemma subst_id': forall h φ x,
    substitution' h (var x) x φ = φ.
Proof.
  induction h; intros; simpl; try reflexivity.
  case φ; intros.
  - case_eq (string_dec x s); intros; simpl; try subst; trivial.
  - induction l; simpl; try reflexivity.
    inversion IHl. rewrite H0. rewrite H0.
    rewrite IHh. reflexivity.
  - rewrite IHh. reflexivity.
  - rewrite IHh, IHh. reflexivity.
  - case_eq (string_dec x s); intros; try rewrite IHh; reflexivity.
Qed.

Fixpoint max_list (l : list nat) :=
  match l with
  | nil => 0
  | cons x xs => let y := (max_list xs) in (if (leb x y) then y else x)
  end.

Fixpoint height (p : Pattern) :=
  match p with
  | var s => 1
  | symbol s ss => 1 + max_list (map height ss)
  | not s => 1 + (height s)
  | and a b => 1 + max_list (map height [a;b])
  | Exists y ψ => 1 + (height ψ)
  end.

Definition substitution (φ' : Pattern) (x : string) (φ : Pattern) : Pattern :=
  substitution' (height φ) φ' x φ.

Lemma subst_id: forall φ x, substitution (var x) x φ = φ.
Proof. unfold substitution. intros. apply subst_id'. Qed.

(* One-to-one conjunction for lists *)
Fixpoint list_conjunction (tᵢ tᵢ' : list Pattern) : option Pattern :=
  match tᵢ, tᵢ' with
  | [], [] => Some ⊤
  | _, []  => None
  | [], _  => None
  | t :: l, t' :: l' => match (list_conjunction l l') with
                          | None => None
                          | Some φ => Some ((t == t') ∧ φ)
                          end
  end.

Lemma list_conjunction_helper : forall tᵢ tᵢ',
    (length tᵢ) = (length tᵢ') ->
    exists ψ, (list_conjunction tᵢ tᵢ') = Some ψ.
Proof.
  induction tᵢ; intros.
  - exists ⊤.
    induction tᵢ'; simpl. reflexivity.
    simpl in H. inversion H.
  - induction tᵢ'; simpl in H. inversion H.
    inversion H. apply IHtᵢ in H1. destruct H1 as (ψ & H1).
    exists (a == a0 ∧ ψ).
    simpl. rewrite H1. reflexivity.
Qed.




(* ******************************************************************************* *)
(* Axioms and Rules of the ML proof system: only a subset of the rules of the      *)
(* ML proof system are used.                                                       *)
(* ******************************************************************************* *)
Inductive step (Γ : list Pattern) (φ : Pattern) : Prop :=
| premise : In φ Γ -> step Γ φ
| mp : forall φ', step Γ (φ' → φ) -> step Γ φ' -> step Γ φ.
Notation "A ⊢ B" := (step A B) (at level 85).

Axiom axiom₁ :
  forall Γ φ φ',
    Γ ⊢ (φ → (φ' → φ)).
Axiom axiom₂ :
  forall Γ φ φ' φ'',
    Γ ⊢ ((φ → (φ' → φ'')) → ((φ → φ') → (φ → φ''))) .
Axiom axiom₃ :
  forall Γ φ φ',
    Γ ⊢ (¬ φ → ¬ φ') → (φ' → φ).
Axiom equality_elimination:
  forall Γ φ φ₁ φ₂ x,
    Γ ⊢ ((φ₁ == φ₂) ∧ (substitution φ₁ x φ)) → (substitution φ₂ x φ).
Axiom eq_membership:
  forall Γ φ φ',
    Γ ⊢ (φ ∈ φ') == (φ == φ').
Axiom definedness_axiom :
  forall Γ φ,
    Γ ⊢ φ -> Γ ⊢ ⌈ φ ⌉.
Axiom totality_axiom :
  forall Γ φ,
    Γ ⊢ φ -> Γ ⊢ ⌊ φ ⌋.
Axiom injectivity:
  forall Γ f args args',
    exists ψ, Some ψ  = (list_conjunction args args') /\
      (Γ ⊢ ((f args) == (f args')) → ψ).
Axiom equal_refl: forall Γ φ,
    Γ ⊢ φ == φ.
(* ******************************************************************************* *)
(* End ML proof rules and axioms                                                   *)
(* ******************************************************************************* *)



(* ******************************************************************************* *)
(* Helper lemmas and theorems                                                      *)
(* ******************************************************************************* *)
Lemma conjunction_as_implication : forall Γ φ φ',
    Γ ⊢ ¬ (φ → ¬ φ') <-> Γ ⊢ φ ∧ φ'.
Proof.
  split; intros; rewrite implies_or, <- or_and in *; assumption.
Qed.

Lemma refl : forall Γ φ, Γ ⊢ φ → φ.
Proof.
  intros.

  assert (Γ ⊢ (φ → ((φ → φ) → φ)) → ((φ → (φ → φ)) → (φ → φ))).
  apply axiom₂.

  assert (Γ ⊢ (φ → ((φ → φ) → φ))).
  apply axiom₁.

  assert (Γ ⊢ ((φ → (φ → φ)) → (φ → φ))).
  apply mp with (φ' := (φ → ((φ → φ) → φ))); assumption.

  assert (Γ ⊢ (φ  → (φ → φ))).
  apply axiom₁.

  apply mp with (φ' := (φ  → (φ → φ))); assumption.
Qed.


Theorem transitivity : forall Γ φ φ' φ'',
    Γ ⊢ φ → φ' ->
    Γ ⊢ φ' → φ'' ->
    Γ ⊢ φ → φ''.
Proof.
  intros.

  assert (Γ ⊢ (φ' → φ'') → (φ → (φ' → φ''))).
  apply axiom₁.
  
  assert (Γ ⊢ (φ → (φ' → φ''))).
  apply mp with (φ' := φ' → φ''); assumption.

  assert (Γ ⊢ (φ → (φ' → φ'')) → ((φ → φ') → (φ → φ''))).
  apply axiom₂.

  assert (Γ ⊢ ((φ → φ') → (φ → φ''))).
  apply mp with (φ' := (φ → (φ' → φ''))); assumption.

  apply mp with (φ' := (φ → φ')); assumption.
Qed.

(* A particular instance of the deduction theorem for the (sub-)proof system of Matching Logic shown in this file. *)
Lemma DT₁ : forall Γ φ φ',
    φ :: Γ ⊢ φ' ->
    Γ ⊢ φ → φ'.
Proof.
  intros.
  induction H.
  - simpl in H. destruct H.
    + subst. apply refl.
    + assert (Γ ⊢ φ0 → (φ → φ0)).
      apply axiom₁.

      assert (Γ ⊢ φ0).
      apply premise. assumption.

      apply mp with (φ' := φ0); assumption.
  - assert (Γ ⊢ φ → (φ' → φ0) → ((φ → φ') → (φ → φ0))).
    apply axiom₂.

    assert (Γ ⊢ (φ → φ') → (φ → φ0)).
    apply mp with (φ' := φ → (φ' → φ0)); assumption.

    apply mp with (φ' := φ → φ'); assumption.
Qed.

Lemma DT₂ : forall Γ φ φ',
    Γ ⊢ φ → φ' -> 
    φ :: Γ ⊢ φ'.
Proof.
  intros.

  assert (φ :: Γ ⊢ φ).
  apply premise. simpl. left. reflexivity.

  assert (φ :: Γ ⊢ φ → φ').
  induction H.
  - apply premise. simpl. right. assumption.
  - apply mp with (φ' := φ'0); assumption.
  - apply mp with (φ' := φ); assumption.
Qed.

Theorem DT : forall Γ φ φ',
    Γ ⊢ φ → φ' <-> φ :: Γ ⊢ φ'.
Proof.
  split; intros.
  apply DT₂; assumption.
  apply DT₁; assumption.
Qed.
  

Lemma negation_consequence : forall Γ φ φ',
    Γ ⊢ ¬ φ → (φ → φ').
Proof.
  intros.

  apply DT.

  assert ((¬ φ) :: Γ ⊢ ((¬ φ') → ¬ φ) → (φ → φ')).
  apply axiom₃.

  assert ((¬ φ) :: Γ ⊢ ¬ φ → ((¬ φ') → ¬ φ)).
  apply axiom₁.

  assert ((¬ φ) :: Γ ⊢ ¬ φ).
  apply premise. simpl. left. reflexivity.

  assert ((¬ φ) :: Γ ⊢ ((¬ φ') → ¬ φ)).
  apply mp with (φ' := ¬ φ) in H0; assumption.

  apply mp with (φ' := ¬ φ' → ¬ φ); assumption.
Qed.

Lemma double_negation_elimination : forall Γ φ,
    Γ ⊢ (¬ ¬ φ) → φ.
Proof.
  intros.

  apply DT.

  assert ((¬ ¬ φ) :: Γ ⊢ ¬ ¬ φ).
  apply premise. simpl. left. reflexivity.

  assert ((¬ ¬ φ) :: Γ ⊢ (¬ ¬ φ) → ((¬ ¬ ¬ ¬ φ) → (¬ ¬ φ))).
  apply axiom₁.

  assert ((¬ ¬ φ) :: Γ ⊢ (¬ ¬ ¬ ¬ φ) → (¬ ¬ φ)).
  apply mp with (φ' := (¬ ¬ φ)); assumption.

  assert ((¬ (¬ φ)) :: Γ ⊢ ((¬ ¬ ¬ ¬ φ) → ¬ (¬ φ)) → ((¬ φ) → (¬ ¬ ¬ φ))).
  apply axiom₃.

  assert ((¬ (¬ φ)) :: Γ ⊢ (¬ φ) → ¬ ¬ ¬ φ).
  apply mp with (φ' := (¬ ¬ ¬ ¬ φ) → ¬ (¬ φ)); assumption.

  assert ((¬ (¬ φ)) :: Γ ⊢ ((¬ φ) → ¬ (¬ (¬ φ))) → ((¬ ¬ φ) → φ)).
  apply axiom₃.

  assert ((¬ ¬ φ) :: Γ ⊢  ((¬ ¬ φ) → φ)).
  apply mp with (φ' := ((¬ φ) → ¬ (¬ (¬ φ)))); assumption.

  apply mp with (φ' := ¬ ¬ φ); assumption.
Qed.

Lemma negation_elimination : forall Γ φ,
    Γ ⊢ (¬ ¬ φ) -> Γ ⊢ φ.
Proof.
  intros.

  assert (Γ ⊢ (¬ ¬ φ) → φ).
  apply double_negation_elimination.

  apply mp with (φ' := (¬ ¬ φ)); assumption.
Qed.


Lemma hypotheses_collapse : forall Γ φ φ',
    φ :: φ :: Γ ⊢ φ' ->
    φ :: Γ ⊢ φ'.
Proof.
  intros.

  induction H.
  - simpl in H. destruct H as [H | [H | H]]; subst.
    apply premise. simpl. left. reflexivity.
    apply premise. simpl. left. reflexivity.
    apply premise. simpl. right. assumption.
  - apply mp with (φ' := φ'); assumption.
Qed.
    
   

Lemma double_negation_intro : forall Γ φ,
    Γ ⊢ φ → ¬ ¬ φ.
Proof.
  intros.

  assert (φ :: Γ ⊢ (φ → ((¬ ¬ ¬ φ) → φ))).
  apply axiom₁.

  assert (φ :: Γ ⊢ φ).
  apply premise. simpl. left. reflexivity.

  assert (φ :: Γ ⊢ (¬ ¬ ¬ φ) → φ).
  apply mp with (φ' := φ); assumption.

  assert (φ :: Γ ⊢ ¬ (¬ (¬ φ)) → ¬ φ).
  apply double_negation_elimination.

  assert (φ :: Γ ⊢ ((¬ ¬ ¬ φ) → ¬ φ) → (φ → (¬ ¬ φ))).
  apply axiom₃.

  assert (φ :: Γ ⊢ (φ → (¬ ¬ φ))).
  apply mp with (φ' := ¬ (¬ (¬ φ)) → ¬ φ); assumption.

  apply DT. rewrite DT in H4.
  apply hypotheses_collapse.
  assumption.
Qed.

Lemma negation_introduction : forall Γ φ,
    Γ ⊢ φ ->
    Γ ⊢ (¬ ¬ φ).
Proof.
  intros.

  assert (Γ ⊢ φ → ¬ ¬ φ).
  apply double_negation_intro.

  apply mp with (φ' := φ); assumption.
Qed.

Lemma implication_negation : forall Γ φ φ',
    Γ ⊢ (φ → φ') → ((¬ ¬ φ) → ¬ ¬ φ').
Proof.
  intros.
  
  apply DT.
  assert ((φ → φ') :: Γ ⊢ (¬ ¬ φ) → φ).
  apply double_negation_elimination.      
  
  assert ((φ → φ') :: Γ ⊢ φ → φ').
  apply premise. simpl. left. reflexivity.
  
  assert ((φ → φ') :: Γ ⊢ ¬ (¬ φ) → φ').
  apply transitivity with (φ' := φ); assumption.
  
  assert ((φ → φ') :: Γ ⊢ φ' → (¬ ¬ φ')).
  apply double_negation_intro.
  
  apply transitivity with (φ' := φ'); assumption.
Qed.


Lemma contraposition_helper: forall Γ φ φ',
    Γ ⊢ (φ' → φ) → (¬ φ → ¬ φ').
Proof.
  intros.

  assert (Γ ⊢ ((¬ ¬ φ') → (¬ ¬ φ)) → (¬ φ → ¬ φ')).
  apply axiom₃.

  assert (Γ ⊢ (φ' → φ) → ((¬ ¬ φ') → (¬ ¬ φ))).
  apply implication_negation.
  apply transitivity with (φ' := ((¬ ¬ φ') → (¬ ¬ φ))); assumption.
Qed.


  

Lemma hypothesis_swap : forall Γ φ φ' ψ,
    φ :: φ' :: Γ ⊢ ψ ->
    φ' :: φ :: Γ ⊢ ψ.
Proof.
  intros.
  induction H.
  - simpl in H. destruct H as [H | [H | H]]; subst.
    apply premise. simpl. right. left. reflexivity.
    apply premise. simpl. left. reflexivity.
    apply premise. simpl. right. right. assumption.
  - apply mp with (φ' := φ'0); assumption.
Qed.


Lemma and_elim_right : forall Γ φ φ',
    Γ ⊢ ¬ (φ → ¬ φ') → φ.
Proof.
  intros.

  assert (Γ ⊢ ¬ φ → (φ → ¬ φ')).
  apply negation_consequence.

  assert (Γ ⊢ (φ → ¬ φ') → ¬ ¬ (φ → ¬ φ')).
  apply double_negation_intro.

  assert (Γ ⊢ ¬ φ → ¬ ¬ (φ → ¬ φ')).
  apply transitivity with (φ' := (φ → ¬ φ')); assumption.

  assert (Γ ⊢ ((¬ φ) → ¬ (¬ (φ → ¬ φ'))) → (¬ (φ → ¬ φ') → φ)).
  apply axiom₃.

  apply mp with (φ' := (¬ φ → ¬ (¬ (φ → ¬ φ')))); assumption.
Qed.


Lemma modus_tollens : forall Γ φ φ',
    Γ ⊢ φ → φ' ->
    Γ ⊢ ¬ φ' ->
    Γ ⊢ ¬ φ.
Proof.
  intros.

  assert (Γ ⊢ (φ → φ') → (¬ φ' → ¬ φ)).
  apply contraposition_helper.
  
  assert (Γ ⊢ (¬ φ' → ¬ φ)).
  apply mp with (φ' := (φ → φ')); assumption.

  apply mp with (φ' := ¬ φ'); assumption.
Qed.

Lemma and_comm : forall Γ φ φ',
    Γ ⊢ ¬ (φ → ¬ φ') ->
    Γ ⊢ ¬ (φ' → ¬ φ).
Proof.
  intros.

  assert (φ :: (φ' → ¬ φ) :: Γ ⊢ φ).
  apply premise. simpl. left. reflexivity.
  assert (φ :: (φ' → ¬ φ) :: Γ ⊢ (φ' → ¬ φ)).
  apply premise. simpl. right. left. reflexivity.

  assert (Γ ⊢ (φ' → ¬ φ) → (φ → ¬ φ')).
  apply DT. apply DT.
  apply modus_tollens with (φ' := (¬ φ)). assumption.
  apply negation_introduction. assumption.

  assert (Γ ⊢ ((φ' → ¬ φ) → (φ → ¬ φ')) → (¬ (φ → ¬ φ') → ¬ (φ' → ¬ φ))).
  apply contraposition_helper.

  assert (Γ ⊢ ¬ (φ → ¬ φ') → ¬ (φ' → ¬ φ)).
  apply mp with (φ' := ((φ' → ¬ φ) → (φ → ¬ φ'))); assumption.

  apply mp with (φ' := (¬ (φ → ¬ φ'))); assumption.
Qed.


(* paper and_elimination_right: Γ ⊢ (φ ∧ φ') -> Γ ⊢ φ *)
Lemma and_elimination_right : forall Γ φ φ',
    Γ ⊢ φ ∧ φ' ->
    Γ ⊢ φ.
Proof.
  intros.

  apply conjunction_as_implication in H.

  assert (Γ ⊢ ¬ (φ → ¬ φ') → φ).
  apply and_elim_right.

  apply mp with (φ' := ¬ (φ → ¬ φ')); assumption.
Qed.

(* paper and_elimination_left: Γ ⊢ (φ ∧ φ') -> Γ ⊢ φ' *)
Lemma and_elimination_left : forall Γ φ φ',
    Γ ⊢ φ ∧ φ' ->
    Γ ⊢ φ'.
Proof.
  intros.
  rewrite <- conjunction_as_implication in H.
  apply and_comm in H.
  rewrite conjunction_as_implication in H.
  apply and_elimination_right with (φ' := φ).
  assumption.
Qed.


Lemma and_intro : forall Γ φ φ',
    Γ ⊢ φ ->
    Γ ⊢ φ' ->
    Γ ⊢ ¬ (φ → ¬ φ').
Proof.
  intros.

  assert ((φ → ¬ φ') :: φ :: Γ ⊢ φ).
  apply premise. simpl. right. left. reflexivity.

  assert (φ :: Γ ⊢ (φ → ¬ φ') → ¬ φ').
  apply DT. 
  
  assert ((φ → ¬ φ') :: φ :: Γ ⊢ (φ → ¬ φ')).
  apply premise. simpl. left. reflexivity.

  apply mp with (φ' := φ); assumption.

  assert (φ :: Γ ⊢ ((φ → ¬ φ') → ¬ φ') → ((¬ ¬ φ') → ¬ (φ → ¬ φ'))).
  apply contraposition_helper.

  assert (φ :: Γ ⊢ (¬ (¬ φ') → ¬ (φ → ¬ φ'))).
  apply mp with (φ' := ((φ → ¬ φ') → ¬ φ')); assumption.

  assert ( φ :: Γ ⊢ φ' → ¬ (¬ φ')).
  apply double_negation_intro.

  assert (φ :: Γ ⊢ φ' → ¬ (φ → ¬ φ')).
  apply transitivity with (φ' :=  ¬ (¬ φ')); assumption.
  rewrite <- DT in H6.

  assert (Γ ⊢ φ' → ¬ (φ → ¬ φ')).
  apply mp with (φ' := φ); assumption.
  apply mp with (φ' := φ'); assumption.
Qed.

Lemma and_introduction : forall Γ φ φ',
    Γ ⊢ φ ->
    Γ ⊢ φ' ->
    Γ ⊢ φ ∧ φ'.
Proof.
  intros.

  apply conjunction_as_implication.
  apply and_intro; assumption.
Qed.
  
Lemma and_commutative: forall Γ φ φ',
    Γ ⊢ φ ∧ φ' ->
    Γ ⊢ φ' ∧ φ.
Proof.
  intros.

  assert (Γ ⊢ φ).
  apply and_elimination_right with (φ' := φ'). assumption.

  assert (Γ ⊢ φ').
  apply and_elimination_left with (φ := φ). assumption.

  apply and_introduction; assumption.
Qed.

Lemma double_negation: forall Γ φ,
    Γ ⊢ φ ↔ ¬ ¬ φ.
Proof.
  intros.

  rewrite equivalence. rewrite <- conjunction_as_implication.
  
  assert (Γ ⊢ (φ → ¬ (¬ φ))).
  apply double_negation_intro.

  assert (Γ ⊢ (¬ (¬ φ) → φ)).
  apply double_negation_elimination.

  apply and_intro; assumption.
Qed.


Lemma equiv_symmetry: forall Γ φ φ',
    Γ ⊢ φ ↔ φ' ->
    Γ ⊢ φ' ↔ φ.
Proof.
  intros.

  rewrite equivalence.
  apply and_commutative.
  rewrite <- equivalence.
  assumption.
Qed.

(* ******************************************************************************* *)
(* End helper lemmas and theorems                                                  *)
(* ******************************************************************************* *)




(* **************************************************** *)
(* Paper proofs                                         *)
(* **************************************************** *)


(* Δ₁ : delete *)
Lemma Δ₁ : forall Γ φ t,
    Γ ⊢ (φ ∧ (t == t)) → φ.
Proof.
  intros.

  apply DT.

  assert ((φ ∧ t == t) :: Γ ⊢ (φ ∧ t == t)).
  apply premise. simpl. left. reflexivity.

  assert ((φ ∧ t == t) :: Γ ⊢ φ).
  apply and_elimination_right with (φ' := t == t); assumption.
  assumption.
Qed.


(* Δ₂ : Decomposition *)
Lemma Δ₂ : forall Γ φ f args args',
    (length args = length args') ->
    exists ψ,
      (Some ψ = (list_conjunction args args')) /\
      (Γ ⊢ (φ ∧ (f args) == (f args')) → (φ ∧ ψ)).
Proof.
  intros.

  apply list_conjunction_helper in H.
  destruct H as (ψ & H).
  exists ψ. split. rewrite H. reflexivity.

  apply DT.
  assert ((φ ∧ f args == f args') :: Γ ⊢ (φ ∧ f args == f args')).
  apply premise. left. simpl. reflexivity.

  assert ((φ ∧ f args == f args') :: Γ ⊢ φ).
  apply and_elimination_right with (φ' :=  f args == f args'). assumption.

  assert ((φ ∧ f args == f args') :: Γ ⊢ (f args == f args')).
  apply and_elimination_left with (φ := φ). assumption.
  
  assert (E: exists ψ', (Some ψ' = list_conjunction args args') /\ ((φ ∧ f args == f args') :: Γ ⊢ (f args == f args') → ψ')).
  apply injectivity. destruct E as (ψ' & E & E').
  rewrite H in E. inversion E. subst. clear E.
  
  assert ((φ ∧ f args == f args') :: Γ ⊢ ψ).
  apply mp with (φ' := (f args == f args')); assumption.

  apply conjunction_as_implication.
  apply and_intro; assumption.
Qed.

Lemma Δ₃ : forall Γ φ f (tᵢ : list Pattern) x,
    Γ ⊢ (φ ∧ (f tᵢ) == (var x)) → (φ ∧ (var x) == (f tᵢ)).
Proof.
  intros.
  rewrite equal_symmetry.
  apply refl.
Qed.

Lemma Δ₄: forall Γ φ x t,
    Γ ⊢ (φ ∧ (var x) == t) → ((substitution t x φ) ∧ (var x) == t).
Proof.
  intros.

  assert ((φ ∧ var x == t) :: Γ  ⊢ (φ ∧ var x == t)).
  apply premise. simpl. left. reflexivity.

  assert ((φ ∧ var x == t) :: Γ  ⊢ φ).
  apply and_elimination_right with (φ' := var x == t). assumption.

  assert ((φ ∧ var x == t) :: Γ  ⊢ var x == t).
  apply and_elimination_left with (φ := φ). assumption.

  rewrite <- subst_id with (x := x) in H0.
  assert ((φ ∧ var x == t) :: Γ ⊢ (var x == t) ∧ (substitution (var x) x φ) →  substitution t x φ).
  apply equality_elimination.

  assert ((φ ∧ var x == t) :: Γ ⊢ (var x == t) ∧ (substitution (var x) x φ)).
  apply and_introduction; assumption.

  assert ((φ ∧ var x == t) :: Γ ⊢ substitution t x φ).
  apply mp with (φ' := (var x == t ∧ substitution (var x) x φ)); assumption.

  apply DT. apply and_introduction; assumption.
Qed.


Lemma Prop₃_left: forall Γ ϕ ϕ',
    Γ ⊢ ϕ ∧ (ϕ == ϕ') → (ϕ ∧ ϕ').
Proof.
  intros.

  assert ((ϕ ∧ ϕ == ϕ') :: Γ ⊢ ϕ ∧ (ϕ == ϕ')).
  apply premise. simpl. left. reflexivity.

  assert ((ϕ ∧ ϕ == ϕ') :: Γ ⊢ ϕ).
  apply and_elimination_right with (φ' := (ϕ == ϕ')). assumption.
  
  assert ((ϕ ∧ ϕ == ϕ') :: Γ ⊢ (ϕ == ϕ')).
  apply and_elimination_left with (φ := ϕ). assumption.
  rewrite <- equal_equiv in H1 at 2.

  assert ((ϕ ∧ ϕ == ϕ') :: Γ ⊢ ϕ → ϕ').
  rewrite equivalence in H1.
  apply and_elimination_right with (φ' := (ϕ' → ϕ)); assumption.

  assert ((ϕ ∧ ϕ == ϕ') :: Γ ⊢ ϕ').
  apply mp with (φ' := ϕ); assumption.

  apply DT.
  apply and_introduction; assumption.
Qed.

Lemma Prop₃_right: forall Γ ϕ ϕ',
    Γ ⊢ (ϕ ∧ ϕ') → (ϕ ∧ (ϕ == ϕ')).
Proof.
  intros.

  apply DT.
  assert ((ϕ ∧ ϕ') :: Γ ⊢ ϕ ∧ ϕ').
  apply premise. simpl. left. reflexivity.

  assert ((ϕ ∧ ϕ') :: Γ ⊢ ⌈ ϕ ∧ ϕ' ⌉).
  apply definedness_axiom. assumption.
  rewrite membership_helper in H0.

  
  assert ((ϕ ∧ ϕ') :: Γ ⊢ (ϕ ∈ ϕ') == (ϕ == ϕ')).
  apply eq_membership.
  rewrite <- equal_equiv in H1.
  rewrite equivalence in H1.

  assert ((ϕ ∧ ϕ') :: Γ ⊢ (ϕ ∈ ϕ' → ϕ == ϕ')).
  apply and_elimination_right with (φ' := (ϕ == ϕ' → ϕ ∈ ϕ')). assumption.

  assert ((ϕ ∧ ϕ') :: Γ ⊢ ϕ == ϕ').
  apply mp with (φ' := ϕ ∈ ϕ'); assumption.

  assert ((ϕ ∧ ϕ') :: Γ ⊢ ϕ ).
  apply and_elimination_right with (φ' := ϕ'). assumption.

  apply and_introduction; assumption.
Qed.

Corollary Prop₃: forall Γ φ φ',
    Γ ⊢ (φ ∧ φ') ↔ (φ ∧ (φ == φ')).
Proof.
  intros. rewrite equivalence.
  apply and_introduction.
  apply Prop₃_right.
  apply Prop₃_left.
Qed.