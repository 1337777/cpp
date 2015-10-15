(** remove printing ~ *)
(** printing ~ %\ensuremath{\sim}% *)

(** * Maclane Associative Coherence *)

(* begin hide *)
Require Import CpdtTactics.
Require Import coherence.
Require Import coherence2.
Set Implicit Arguments.
Inductive List := .
(* end hide *)

(** This %\textsc{%Coq%}% text shows the semiassociativity completeness and coherence internal some encoding where associative coherence is the meta :

    %\textsc{%Maclan pentagon is some recursive square !!%}% This recursive square [normalize_map_assoc] is the "functorial" parallel to the normalization/flattening of binary trees; and is simply the unit of the reflection for the adjunction.

    The associative coherence comes before anything else, before the semiassociative completeness and before the semiassociative coherence :
%\\%  * The associative coherence, by the recursive square lemma, critically reduce to the classification of the endomorphisms in the semiassociative category. 
%\\% * This associative coherence do not lack some "Newman-style" diamon lemma. The comonadic  adjunction, embedding : [arrows] $\leftrightarrows$ [arrows_assoc] : flattening reflection, which says/subgeres that semiassociative coherence covers (and temporarily comes before) associative coherence is actually done posterior-ly (for want of formality), after it is already known that the simpler [List] subcategory of [arrows] made of endomorphisms is enough to cover (and is equivalent to) [arrows_assoc].
%\\% * The semiassociative coherence do lack some "Newman-style" diamon lemma; and, again posterior-ly, there exists some monadic adjunction, embedding : [List] $\leftrightarrows$ [arrows] : flattening reflection.

    The associative category is the meta of the semiassociative category, and the phrasing of semiassociative completeness [lemma_completeness] shows this actuality very clearly. The semiassociative coherence is done in some internal ( "first/second order" ?? ) encoding relative to associative coherence; may be exists some (yet to be found) "higher-order" / Coq Gallina encoding. The semiassociative coherence do lack some "Newman-style" diamon lemma. This diamon lemma is done in somme two-step process : first the codomain object of the diamon is assumed to be in normal/flattened form and this particularized diamon lemma [lemma_directedness] is proved without holding semiassociative completeness; then this assumption is erased and the full diamon lemma [lemma_coherence0] now necessitate the semiassociative completeness.

    Dosen book %\cite{dosen}% section 4.2 then section 4.3 is written into some computationally false order/precedence. The source of this falsification is the confusion/mixup between "convertible" (definitionality/meta equal) or "propositional equal" where the things are local variables instead of fully constructor-ed explicit terms.

    These Coq texts do not necessitate impredicativity and do not necessitate limitation of the flow of information from proof to data and do not necessitate large inductive types with polymorphic constructors and do not necessitate universe polymorphism; therefore no distinction between [Prop] or [Set] or [Type] is made in these Coq texts. Moreover this Coq text does not hesitate to use the very sensible/fragile library [Program.Equality] [dependent destruction] which may introduce extra non-necessary [eq_rect_eq] axioms. It is most possible to erase this [eq_rect_eq] ( coherence !! .. ) axiom from this Coq texts, otherwise this would be some coherence problem as deep/basic as associative coherence or semiassociative coherence. At the very least it is known that the recursive square [normalize_map_assoc] does not hold [eq_rect_eq] and is closed under the global context.

    Noson Yanofsky talks about some Catalan categories to solve associative coherence in hes doctor text, may be the "functorial" normalization/flattening here is related to hes Catalan categories. Also the [AAC tactics] or [CoqMT] which already come with COQ may be related, but the ultimate motivation is different ... *)

(* begin hide *)
Infix "/\0" := (up_0) (at level 59, right associativity).
Print objects.
(** %\vspace{-.15in}%  [[
Inductive objects : Set :=
    letter : letters -> objects | /\0 : objects -> objects -> objects.
]]
*)
Infix "~a" := same_assoc (at level 69).
Print same_assoc.
(* end hide *)
(** %\vspace{-.15in}% [[
Inductive same_assoc : forall A B : objects, arrows_assoc A B -> arrows_assoc A B -> Set
 := same_assoc_refl : forall (A B : objects) (f : arrows_assoc A B), f ~a f
 | ...
 | same_assoc_bracket_left_5 : forall A B C D : objects,
   bracket_left_assoc (A /\0 B) C D <oa bracket_left_assoc A B (C /\0 D) ~a
   bracket_left_assoc A B C /\1a unitt_assoc D <oa bracket_left_assoc A (B /\0 C) D <oa
   unitt_assoc A /\1a bracket_left_assoc B C D.
]]
*)
(* begin hide *)
Infix "~s" := same' (at level 69).
About same'.
Print normal.
(* end hide *)
(** %\vspace{-.15in}% [[
Inductive normal : objects -> Set :=
normal_cons1 : forall l : letters, normal (letter l)
| normal_cons2 : forall (A : objects) (l : letters), normal A -> normal (A /\0 letter l).
]]
*)
(* begin hide *)
Print normalize_aux.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint normalize_aux (Z A : objects) {struct A} : objects :=
  match A with
    | letter l => Z /\0 letter l
    | A1 /\0 A2 => (Z </\0 A1) </\0 A2
  end
where "Z </\0 A" := (normalize_aux Z A).
]]
*)
(* begin hide *)
Print normalize.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint normalize (A : objects) : objects :=
  match A with
    | letter l => letter l
    | A1 /\0 A2 => (normalize A1) </\0 A2
  end.
]]
*)
(** Roughtly, the lemma [development] takes as input some arrow term (bracket /\ bracket) and output some [developed] arrow term (bracket /\ 1) o (1 /\ bracket) which is [~s] convertible (essentially by bifunctoriality of /\) to the input. Now surprisingly, this [development] or factorization lemma necessitate some deep (`well-founded') induction, using some measure [length] which shows that this may be related to arithmetic factorization. *)

(* begin hide *)
Print developed.
Print length.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint length (A B : objects) (f : arrows A B) {struct f} : nat :=
  match f with
  | unitt _ => 2
  | bracket_left _ _ _ => 4
  | up_1 A0 B0 A1 B1 f1 f2 => length A0 B0 f1 * length A1 B1 f2
  | com A B C f1 f2 => length A B f1 + length B C f2
  end.
]]
*)
(* begin hide *)
About development.
(* end hide *)
(** %\vspace{-.15in}% [[
Lemma development : forall (len : nat) (A B : objects) (f : arrows A B),
       length f <= len -> { f' : arrows A B &
                                  developed f' * ((length f' <= length f) * (f ~s f')) }.
]]
*)
(* begin hide *)
(* Print developed_normal.
Print developed_normalize. *)
(* end hide *)
(* begin hide *)
(* begin courtesy cleanup *)
Notation normalize_aux_unitrefl := normalize_aux_arrow.
Notation normalize_unitrefl := normalize_arrow.
(* end courtesy cleanup *)
(* end hide *)
(* begin hide *)
Notation normalize_aux_unitrefl_assoc := normalize_aux_arrow_assoc.
Infix "</\1a" := (normalize_aux_unitrefl_assoc).
Print normalize_aux_arrow_assoc.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint normalize_aux_unitrefl_assoc Y Z (y : arrows_assoc Y Z) A 
 : arrows_assoc (Y /\0 A) (Z </\0 A) :=
  match A with
    | letter l => y /\1a unitt_assoc (letter l)
    | A1 /\0 A2 => ((y </\1a A1) </\1a A2) <oa bracket_left_assoc Y A1 A2
  end
where "y </\1a A" := (normalize_aux_unitrefl_assoc y A).
]]
*)
(* begin hide *)
Notation normalize_unitrefl_assoc := normalize_arrow_assoc.
Print normalize_arrow_assoc.
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint normalize_unitrefl_assoc (A : objects) : arrows_assoc A (normalize A) :=
  match A with
    | letter l => unitt_assoc (letter l)
    | A1 /\0 A2 => (normalize_unitrefl_assoc A1) </\1a A2
  end.
]]
*)
Check th151 : forall A : objects, normal A -> normalize A = A.
(** Aborted th270 : for local variable [A] with [normal A],
although there is the propositional equality [th151: normalize A = A], one gets 
that [normalize A] and [A] are not convertible (definitionally/meta equal);
therefore one shall not regard [normalize_unitrefl_assoc A] and [unitt A] as sharing
the same domain-codomain indices of [arrows_assoc]. *)
(* begin hide *)
(* begin explanation *)
Inductive term_unitt_assoc : forall A B : objects, arrows_assoc A B -> Set :=
  term_unitt_assoc_self : forall A : objects,
                            term_unitt_assoc (unitt_assoc A)
| term_unitt_assoc_at_left : forall (A B : objects) (f : arrows_assoc A B),
                               term_unitt_assoc f ->
                               forall A0 : objects,
                                 term_unitt_assoc (f /\1a unitt_assoc A0)
| term_unitt_assoc_at_right : forall (A A0 B0 : objects)
                                     (f : arrows_assoc A0 B0),
                                term_unitt_assoc f ->
                                term_unitt_assoc (unitt_assoc A /\1a f).
Hint Constructors term_unitt_assoc.
Lemma th270_old_corrected : forall A, normal A -> term_unitt_assoc (normalize_unitrefl_assoc A).
  induction 1; crush.
Defined.
(* end explanation *)
(* end hide *)

Check th260 : forall N P : objects, arrows_assoc N P -> normalize N = normalize P.
(** Aborted lemma_coherence_assoc0 : for local variables [N], [P] with [arrows_assoc N P],
although there is the propositional equality [th260 : normalize N = normalize P],
one gets that [normalize N] and [normalize P] are not convertible (definitionally/meta equal);
therefore some transport other than [eq_rect], some coherent transport is lacked. *)

(** Below [directed y] signify that [y] is in the image of the embedding of [arrows] into [arrows_assoc]. *)

(* begin hide *)
Section section_scope.
Open Scope type_scope.
(* end hide *)
Check normalize_aux_map_assoc : forall (X Y : objects) (x : arrows_assoc X Y)
         (Z : objects) (y : arrows_assoc Y Z), directed y ->
       forall (A B : objects) (f : arrows_assoc A B),
       { y_map : arrows_assoc (Y </\0 A) (Z </\0 B) &
       (y_map <oa x </\1a A ~a y </\1a B <oa x /\1a f) * directed y_map }.

Check normalize_map_assoc : forall (A B : objects) (f : arrows_assoc A B),
       { y_map : arrows_assoc (normalize A) (normalize B) &
       (y_map <oa normalize_unitrefl_assoc A ~a
         normalize_unitrefl_assoc B <oa f) * directed y_map }.
(* begin hide *)
Close Scope type_scope.
End section_scope.
(* end hide *)
Print Assumptions normalize_map_assoc.
(** <<
Closed under the global context
>>
*)
(* begin hide *)
Print Assumptions lemma_coherence_assoc.
(**  %\vspace{-.15in}% [[
JMeq.JMeq_eq
Eqdep.Eq_rect_eq.eq_rect_eq
]]
*)
(* end hide *)

(** * Dosen SemiAssociative Coherence *)
(* begin hide *)
Print nodes.
(* end hide *)
(** %\vspace{-.15in}% [[
Inductive nodes : objects -> Set :=
    self : forall A : objects, A
  | at_left : forall A : objects, A -> forall B : objects, A /\0 B
  | at_right : forall A B : objects, B -> A /\0 B.
]]
 *)
(* begin hide *)
Infix "<r" := lt_right (at level 70). 
Print lt_right.
(* end hide *)
(** %\vspace{-.15in}% [[
Inductive lt_right : forall A : objects, A -> A -> Set :=
    lt_right_cons1 : forall (B : objects) (z : B) (C : objects),
                     self (C /\0 B) <r at_right C z
  | lt_right_cons2 : forall (B C : objects) (x y : B),
                     x <r y -> at_left x C <r at_left y C
  | lt_right_cons3 : forall (B C : objects) (x y : B),
                     x <r y -> at_right C x <r at_right C y.
]]
*)
(* begin hide *)
Notation comparable A B := {f : arrows_assoc A B | True} (only parsing).
Lemma bracket_left_on_nodes'
     : forall A B C : objects, nodes (A /\0 (B /\0 C)) -> nodes ((A /\0 B) /\0 C).
  refine (fun (A B C : objects) (x : A /\0 B /\0 C) =>
            match x in nodes X0 return X0 = (A /\0 (B /\0 C)) -> _ with
              | self _ => _
              | at_left _ x0 _ => _
              | at_right _ _ x0 => _
            end eq_refl); intro pf; inversion pf; subst.
  exact (at_left (self (A /\ B)) C ).
  exact (at_left (at_left x0 B) C ).
  
  refine (match x0 in nodes X0 return X0 = (B /\0 C) -> _ with
            | self _ => _
            | at_left _ x1 _ => _
            | at_right _ _ x1 => _
          end eq_refl); intro pf0; inversion pf0; subst.
  exact (self ((A /\ B) /\ C )).
  exact (at_left (at_right A x1) C ).
  exact (at_right (A /\ B) x1). Defined.
Print Assumptions bracket_left_on_nodes'.
(** <<
Closed under the global context
>> *)
Check bracket_left_on_nodes.
(* end hide *)
(** %\vspace{-.15in}% [[
Definition bracket_left_on_nodes (A B C : objects)
 ( x : nodes (A /\0 (B /\0 C)) ) : nodes ((A /\0 B) /\0 C).
    dependent destruction x.
        exact (at_left (self (A /\0 B)) C).
        exact (at_left (at_left x B) C).
        dependent destruction x.
            exact (self ((A /\0 B) /\0 C)).
            exact (at_left (at_right A x) C).
            exact (at_right (A /\0 B) x). Defined.
]]
*)
Check arrows_assoc_on_nodes : forall A B, arrows_assoc A B -> nodes A -> nodes B.

(** Soundness : (using [nodes] and [arrows_assoc_on_nodes] notations coercions) *)

(* begin hide *)
Notation lemma_soundness := lem033.
(* end hide *)
Check lemma_soundness : forall A B (f : arrows A B) (x y : A), f x <r f y -> x <r y.

(** Completeness : lemma [lem005700] is deep (`well-founded') induction on [lengthn''], with accumulator/continuation [cumul_letteries]. The prerequisites are 4000 lines of multifolded/complicated Coq text , and some of which are listed below. And this Coq text is at minimum as complicated as, and certainly less smooth than, the correctness proofs of the regular expression matcher or the balanced binary-search tree presented in Chlipala CPDT %\cite{chlipalacpdt}% or Harper SMLBOOK %\cite{harper}%. *)

Check lemma_completeness : forall (B A : objects) (f : arrows_assoc B A),
         (forall x y : nodes B, x <r y -> (f x) <r (f y)) -> arrows A B.

Check lem005700 : forall (B : objects) (len : nat),
 forall (cumul_letteries : nodes B -> bool)
 (H_cumul_letteries_wellform : cumul_letteries_wellform' B cumul_letteries)
 (H_cumul_letteries_satur : forall y : nodes B, cumul_letteries y = true
     -> forall z : nodes B, lt_leftorright_eq y z -> cumul_letteries z = true)
 (H_len : lengthn'' cumul_letteries H_cumul_letteries_wellform <= len),
 forall (A : objects) (f : arrows_assoc B A)
 (H_node_is_lettery : forall x : nodes B, cumul_letteries x = true -> node_is_lettery f x)
 (H_object_at_node : forall x : nodes B, cumul_letteries x = true 
     -> object_at_node x = object_at_node (f x))
 (H_cumul_B : forall x y : nodes B, x <r y -> (f x) <r (f y)),    arrows A B.
(* begin hide *)
Print Assumptions lem005700.
(** Get two equivalent axioms. *)
(** [[
JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y
Eqdep.Eq_rect_eq.eq_rect_eq : forall (U : Type) (p : U) (Q : U -> Type)
                                (x : Q p) (h : p = p), x = eq_rect p Q x p h
]]
*)
(* end hide *)
(* begin hide *)
Infix "<l" := lt_left (at level 70). 
Print lt_left.
Print lt_leftorright_eq.
(* end hide *)
(** %\vspace{-.15in}% [[
Notation lt_leftorright_eq x y := (sum (eq x y) (sum (x <l y) (x <r y))).
]]
*)
(** And [nodal_multi_bracket_left_full], which is some localized/deep [multi_bracket_left] at some internal node, is one of the most complicated/multifolded construction in this Coq text. And [nodal_multi_bracket_left_full] below and later really lack this constructive equality [objects_same], so that we get some transport map which is coherent, transport map other than [eq_rect]. Maybe it is possible to effectively  use the constructive equality [objects_same] at more places instead of [eq]. *)

(* begin hide *)
Print objects_same.
(* end hide *)
(** %\vspace{-.15in}% [[
Inductive objects_same : objects -> objects -> Set :=
    objects_same_cons1 : forall l : letters, objects_same (letter l) (letter l)
  | objects_same_cons2 : forall A A' : objects, objects_same A A' ->
                         forall B B' : objects, objects_same B B' ->
                         objects_same (A /\0 B) (A' /\0 B').
]]
*)
(* begin hide *)
Print "/\\".
(* end hide *)
(** %\vspace{-.15in}% [[
Fixpoint foldright (A : objects) (Dlist : list objects) {struct Dlist} : objects :=
  match Dlist with
    | nil => A
    | D0 :: Dlist0 => (A /\\ Dlist0) /\0 D0
where "A /\\ Dlist" := (foldright A Dlist).
]]
*)

Check multi_bracket_left : forall (A B C : objects) (Dlist : list objects),
       arrows (A /\0 (B /\0 C /\\ Dlist)) ((A /\0 B) /\0 C /\\ Dlist).
(* begin hide *)
Check (fun A (x : nodes A) (A2 B2 C2 : objects) (Dlist2 : list objects) =>
    @nodal_multi_bracket_left_full A x A2 B2 C2 Dlist2).
(* end hide *)
(* begin hide *)
Print object_at_node.
(* end hide *)
(**  %\vspace{-.15in}% [[
Fixpoint object_at_node (A : objects) (x : A) {struct x} : objects :=
  match x with
  | self A0 => A0
  | at_left A0 x0 _ => object_at_node A0 x0
  | at_right _ B x0 => object_at_node B x0
  end.
]]
*)
(* begin hide *)
(** And [object_is_letter] and [object_is_tensor] is some particularised sigma type so to do 
convertibility (definitinal/meta equality) instantiatiations instead and avoid
propositional equalities. *)
Print object_is_letter.
(* end hide *)
(** %\vspace{-.15in}% [[
Inductive object_is_letter : objects -> Set :=
    object_is_letter_cons : forall l : letters, object_is_letter (letter l).
]]
*)
(* begin hide *)
Print node_is_letter.
(* end hide *) 
(** %\vspace{-.15in}% [[
Notation node_is_letter x := (object_is_letter (object_at_node x)). 
]]
*)
(* begin hide *)
Print object_is_tensor.
Print node_is_tensor.
(** %\vspace{-.15in}% [[
Notation node_is_tensor x := (object_is_tensor (object_at_node x)).
]]
*)
Print node_is_lettery.
(* end hide *)
(** %\vspace{-.15in}% [[
Notation node_is_lettery f w := (prod
( forall (x : nodes _), lt_leftorright_eq w x -> lt_leftorright_eq (f w) (f x) )
( forall (x : nodes _), lt_leftorright_eq (f w) (f x) 
      -> lt_leftorright_eq ((rev f) (f w)) ((rev f) (f x)) )).
]]
*)
(* begin hide *)
Print cumul_letteries_wellform'.
(* end hide *)
(** %\vspace{-.15in}% [[
Notation cumul_letteries_wellform' B cumul_letteries :=
  (forall x : B, node_is_letter x -> eq (cumul_letteries x) true).
]]
*)
(* begin hide *)
Print lengthn''.
(* end hide *)
(* begin hide *)
(** %\vspace{-.15in}% [[
Fixpoint lengthn'' (A : objects) (cumul_letteries : A -> bool)
(H_cumul_letteries_wellform : cumul_letteries_wellform' A cumul_letteries){struct A}: nat:=
 match A as o return
 (forall cumul_letteries0 : o -> bool, cumul_letteries_wellform' o cumul_letteries0 -> nat)
 with
  | letter l => fun _ _ => 1
  | A1 /\0 A2 => fun cumul_letteries0 H_cumul_letteries_wellform0 =>
      if Sumbool.sumbool_of_bool (cumul_letteries0 (self (A1 /\0 A2)))
      then 1
      else
       let IHA1 := lengthn'' (restr_left cumul_letteries0)
                  (restr_left_wellform cumul_letteries0 H_cumul_letteries_wellform0) in
       let IHA2 := lengthn'' (restr_right cumul_letteries0)
                 (restr_right_wellform cumul_letteries0 H_cumul_letteries_wellform0) in
       IHA1 + IHA2
  end cumul_letteries H_cumul_letteries_wellform.
]]
*)
Check restr_left : forall B1 B2 : objects, (B1 /\0 B2 -> bool) -> B1 -> bool.  
Check restr_left_wellform : forall (B1 B2 : objects) (cumul_letteries : B1 /\0 B2 -> bool),
       cumul_letteries_wellform' (B1 /\0 B2) cumul_letteries ->
       cumul_letteries_wellform' B1 (restr_left cumul_letteries).
(* end hide *)
(* More at https://github.com/mozert/ . *)