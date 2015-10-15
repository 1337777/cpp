(** SHORT DESCRIPTION       (COQ 8.4pl2)
+ This COQ script present some alternative recursive-datatypes-proof (5000 lines) of the <<semi-associative completeness theorem>> of section 4.2 page 91 of Dosen-Petric book <<proof-theoretical coherence>> http://www.mi.sanu.ac.rs/~kosta/coh.pdf . * the first question is why does such immediate observation has some complicated 5000-lines datatypes-proof? the main claim/thesis of the publication is that this COQ script/proof is necessary and minimal.

+ the basic recursive structure : [letters], [objects], [nodes], [lt_right]
+ every lemma as hint, therefore names of lemmas are numbers
+ comparable objects signify presence of some full-associativity-arrow between the objects, and each arrow in the full-associativity generate some bijection between the nodes of the objects
+ the <<soundness lemma>> is [Lemma lem001700], which says that each semi-associativity-arrow produces some reverse inclusion between the [lt_right] property, then 
+ the <<development/factorization lemma>> is [Lemma development], which holds the particular measure [Fixpoint length] on arrows other than letters-length to do some deep/wellfounded recursion, this <<development lemma>> is not held for the present <<completeness lemma>> but will be held for the <<coherence lemma>> later, and later before doing [Recursive Extraction development.], one shall erase all the logical [Set] occurrences and replace them with Prop
+ then [Lemma lem004000 lem004100 lem004200 lem004300 lem004400] describe how each arrow in the full-associativity generate some bijection between the nodes of the objects
+ then [Lemma lem004500 lem004510 lem004600 lem004700 lem004800] describe the constructive-decidability of whether the reverse inclusion between the [lt_right] properties is proper
+ next is [Fixpoint multi_bracket_specif] and the problems with sigma types and [simpl] start to show, for example: * [destruct] destructing the induction-hypothesis, in contrast with * applying projections [projT1] [projT2] on the induction-hypothesis. Also the difference between the [Fixpoint] and the [Definition]-started-by-[induction]-tactic with reference to the [simpl] tactic start to show.
+ next with [Inductive term_arrow] and [Definition cat_term_arrow_on_nodes_target] and [Definitionnodal_arrow] we start to see local-global-transfer techniques
+ next, while the commands [Scheme Equality for letters.] [Scheme Equality for objects.] automatically works and generate boolean equality and decidable equality for [letters] and [objects], now the command [Scheme Equality for nodes.] will not work for the more complicated property [nodes] and manual definition of [nodes_beq] and [nodes_eq_dec].
+ next the [Definition nodal_multi_bracket_left] dependent nested-pairs is some extension of the [Definition nodal_arrow] dependent nested-pairs for the case where the local arrow is [multi_bracket_left]. the first extension is to say that the [lt_right] property of the two objects of the arrow are the same/co-cumulating except when the lower node is the selected node
+ the remaining basic recursive structures are : [lt_left], [lt_left_once], [lt_right], [lt_right_once], [lt_par], and by necessity the constructive equality [lt_same] for nodes is presented, but this is not held/used later. instead the constructive equality [objects_same] for ojects will be critical later
+ then [Lemma lem006100 lem006200 lem006300 lem006400 lem006500 lem006600 lem006700 lem006800 lem006900 lem007000 lem007100 lem007200 lem007300 lem007300_post lem007400 lem007500 lem007500_rev lem007500_rev' lem007500_rev'' lem008800_pre] are lemmas for comparison between many different combinations of these basic recursive structures
+ then [node_is_letter] property is presented [Lemma lem008100 lem008200 lem008300 lem008400 lem008300' lem008500 lem008600 lem008700_pre] and its weakened [Lemma lem008700] form [Notation node_is_lettery] is presented
+ then from [Lemma lem009700] and its sub-lemmas, the dirty combinatorics begins
+ the step lemmas are [Lemma lem009700_pre6 lem009700_pre6' lem009700], which says that [lt_left_once] is preserved by any full-associativity arrow when the greater node has [node_is_lettery] and the [lt_right] cumul condition is fulfilled. now while [lt_right_once] is not preserved without this [lt_right] cumul condition, we have nevertheless that the property in [Lemma lem009800] hold, which infers that the image node is some right-folding by [Fixpoint foldrightn], but before doing the actual folding we critically lack constructive equality on objects:
+ next, the constructive equality [Inductive objects_same] on objects is critically lacked to solve some <<coherence/commutativity>> problems of the transport map [eq_rect] between [nodes], which is: does [eq_rect] then [at_left] commutes/convertible with [at_left] then [eq_rect] ? next we get the proper transport map [Fixpoint nodes_map] instead of [eq_rect].
+ next, those commutativity problems are resolved in [Lemma lem091 lem099 lem100]
+ now we can do the announced folding by using [Lemma lem009900], which uses the transport map [nodes_map]
+ finally we prepare for the deep/wellfounded recursion in the main lemma [Lemma lem005700].
+ the function [cumul_letteries] from [nodes] to [bool] is some accumulator of currently selected nodes.
+ this accumulator [cumul_letteries] shall be [Notation cumul_letteries_wellform'] which says that all [node_is_letter] are always accumulated.
+ the next node to accumulate is searched and found using [Lemma next_in_cumul_letteries].
+ then the length [Fixpoint lengthn''] of any [cumul_letteries] and its properties are presented.
+ we discover another annoying COQ bug/feature and solve it in [Lemma lem005400''_post'], which is that [auto] tactic is not good at using [apply] which actually decompose the conclusion of some lemma when it is some tuple type, even/same if [apply] alone do decompose this conclusion when typle type.
+ next it is necessary to resolve some extensionally problem, this is done in [Lemma lem005400''_post2]: when two [cumul_letteries] are point-wise same then their [lengthn''] is the same. this signify that we do not lack general/full extensionality axioms.
+ then [Lemma lem010800] and [Lemma lem011000] present the two properties [node_is_lettery] and [object_at_node] which will be transfered onto the node found by [Lemma next_in_cumul_letteries], after we correct the target-object by some [nodal_multi_bracket_left] to get [lt_right_once] instead of only [lt_right]
+ finally for the preparation, the [Definition more_cumul_letteries] takes some [cumul_letteries] and some particular node whose value is [false] and produces some new [cumul_letteries] which sets this node to [true] and whose [lengthn''] is less.
+ we start to notice some <<saturation/algebraic>> techniques because we require as hypothesis for [Definition more_cumul_letteries] that both this particular node and its path of all lesser nodes have value [false]. Also we require as hypothesis for [Lemma lem005700] that [cumul_letteries] be saturated, which is that if some node has value [true] then its cone of all the greater nodes has value [true]. and the proof will not progress without these saturations
+ next [Fixpoint loc_rev] [Fixpoint loc] [Fixpoint loc'] allow to make local-global transfers, for example: [Lemma lem231] shows preservation of [lt_right] from local to global
+ next [Definition list_from_lt_right_once_almost] extends [lem009900] in some more complicated context where two transport maps [nodes_map] are lacked
+ then the goal decompose in two cases: whether the list used by [foldrightn] is empty or non-empty. in the first case, the transfer of the two properties [node_is_lettery] and [object_at_node] onto the node found by [Lemma next_in_cumul_letteries] is immediate. in the second case, before doing this transfer, one has to correct the target-object by some [nodal_multi_bracket_left] to get [lt_right_once] instead of only [lt_right].
+ for the second case, from the start we get some problem with the manner in which the list is folded: one wants to fold the co-head then the co-tail, but we are given and folding the tail then the head. we use [Fixpoint move_foldright] and [Fixpoint move_foldrightn_self] to move the precedence. also remember that the unnamed [lem071] is simply the symmetry form of [nodes_map] as show in [Lemma lem072]
+ we shall also lack more properties of the [nodal_multi_bracket_left], this is why [Definition nodal_multi_bracket_left_full] is presented, which extends the basic dependent nested-pairs [nodal_multi_bracket_left] with more properties
+ finally each step of the proof is done within some separate [assert]
**)

Require Import Coq.Program.Equality.
Require Import Omega.

Set Implicit Arguments .

Inductive letters : Set := letters0 : letters | lettersSucc : letters -> letters.

Inductive objects : Set :=
| letter : letters -> objects
| up_0 : objects -> objects -> objects .

Infix "/\" := up_0 (at level 80, right associativity) . (*/!\ ..*)

Inductive nodes : objects -> Set :=
| self : forall A, nodes A
| at_left : forall {A}, nodes A -> forall B : objects, nodes (A /\ B)
| at_right : forall A : objects, forall {B}, nodes B -> nodes (A /\ B) .

Coercion nodes : objects >-> Sortclass.

Inductive le : forall A, nodes A -> nodes A -> Set :=
| le_self_self : forall A, le (self A) (self A)
| le_self_at_left : forall B C, forall (x : nodes B), le (self (B /\ C)) (at_left x C)
| le_self_at_right : forall B C, forall (x : nodes C), le (self (B /\ C)) (at_right B x)
| le_at_left_at_left  : forall B C, forall (x y : nodes B), le x y -> le (at_left x C) (at_left y C)
| le_at_right_at_right  : forall B C, forall (x y : nodes C), le x y -> le (at_right B x) (at_right B y) .

Inductive lt_for_left : forall A, nodes A -> nodes A -> Set :=
| lt_for_left_self_at_left : forall B C, forall x : nodes B, lt_for_left (self (B /\ C)) (at_left x C)
| lt_for_left_at_left_at_left : forall B C, forall (x y : nodes B), lt_for_left x y -> lt_for_left (at_left x C) (at_left y C)
| lt_for_left_at_right_at_right : forall B C, forall (x y : nodes C), lt_for_left x y -> lt_for_left (at_right B x) (at_right B y) .

Inductive lt_for_right : forall A, nodes A -> nodes A -> Set :=
| lt_for_right_self_at_right : forall B C, forall x : nodes C, lt_for_right (self (B /\ C)) (at_right B x)
| lt_for_right_at_left_at_left : forall B C, forall (x y : nodes B), lt_for_right x y -> lt_for_right (at_left x C) (at_left y C)
| lt_for_right_at_right_at_right : forall B C, forall (x y : nodes C), lt_for_right x y -> lt_for_right (at_right B x) (at_right B y) .

Infix "<e" := le (at level 70).
Infix "<l" := lt_for_left (at level 70). 
Infix "<r" := lt_for_right (at level 70). 

Hint Constructors objects nodes le lt_for_left lt_for_right.

Lemma lem00110 : forall B A, B = (A /\ B) -> Empty_set.

induction B; intros A Heq; simplify_eq Heq; eauto.
Defined.

Lemma lem00210 : forall A B, A = (A /\ B) -> Empty_set.

induction A; intros B Heq; simplify_eq Heq; eauto.
Defined.

Lemma lem00310 : forall A, forall (x : nodes A), x <e x.

induction x; auto.
Defined.

Local Ltac le_lt_trans := 
  fun x y z =>
  induction x;
  dependent destruction y;
  dependent destruction z;
  intros Hxy Hyz;
  solve [ auto
        | dependent destruction Hxy
        | dependent destruction Hyz
        | dependent destruction Hxy;
          dependent destruction Hyz; eauto ].

Lemma lem00410 : forall A, forall (x y z : nodes A), x <e y -> y <e z -> x <e z.

  le_lt_trans x y z.
Defined.
(* Print lem00410. (* 922 lines *) *)

Lemma lem00610 : forall A, forall (x y z : nodes A), x <r y -> y <r z -> x <r z.

  le_lt_trans x y z.
Defined.
(* Print lem00610. (* 1076 lines *) *)

Lemma lem00710 : forall A, forall (x y z : nodes A), x <r y -> y <e z -> x <r z.

  le_lt_trans x y z.
Defined.

Lemma lem01010 : forall A, forall (x y : nodes A), x <r y -> x <e y.

  intros A x y Hxy;
  induction Hxy;
  solve [ auto
        | dependent destruction Hxy
        | dependent destruction Hxy; auto
        ].
Defined.

Lemma lem01110 : forall A, forall (x : nodes A), x <r x -> Empty_set.

  intros A x Hxx;
  dependent induction Hxx; auto.
Defined.

Lemma lem01210 : forall A B, forall (x : nodes A), at_left x B <r self (A /\ B) -> Empty_set.

  intros A B x Hlt;
  dependent destruction Hlt.
Defined.

Lemma lem01310 : forall A, forall x y : nodes A, y <r x -> x <e y -> Empty_set.

  dependent induction x;
  dependent destruction y;
  intros Hyx Hxy;
  solve [ dependent destruction Hyx
        | dependent destruction Hxy
        | dependent destruction Hyx;
          dependent destruction Hxy; eapply IHx; eauto
        ].
Defined.

Hint Resolve lem00110 lem00210 lem00310 lem00410 lem00610 lem00710 lem01010 lem01110 lem01210 lem01310.

Inductive arrows : objects -> objects -> Set :=
| unitt : forall A : objects, arrows A A
| bracket_left : forall A B C : objects, arrows (A /\ (B /\ C)) ((A /\ B) /\ C)
| up_1 : forall A B A0 B0 : objects, arrows A B -> arrows A0 B0 -> arrows (A /\ A0) (B /\ B0)
| com : forall A B C : objects, arrows A B -> arrows B C -> arrows A C.

Notation "g '<o' f" := (@com _ _ _ f g) (at level 99, right associativity). (* very low, just below binders *)

Inductive arrows_assoc : objects -> objects -> Set :=
| unitt_assoc : forall A : objects, arrows_assoc A A
| bracket_left_assoc : forall A B C : objects, arrows_assoc (A /\ (B /\ C)) ((A /\ B) /\ C)
| bracket_right_assoc : forall A B C : objects, arrows_assoc ((A /\ B) /\ C) (A /\ (B /\ C))
| up_1_assoc : forall A B A0 B0 : objects, arrows_assoc A B -> arrows_assoc A0 B0 -> arrows_assoc (A /\ A0) (B /\ B0)
| com_assoc : forall A B C : objects, arrows_assoc A B -> arrows_assoc B C -> arrows_assoc A C.

Infix "/\1" := up_1 (at level 80, right associativity). (* same as /\ above and as logical /\ *)

Hint Constructors arrows arrows_assoc.

Fixpoint arrows_coerce (A B : objects) (f : arrows A B) : arrows_assoc A B.

Proof.
destruct f.
exact (unitt_assoc _).
exact (bracket_left_assoc _ _ _).
exact (up_1_assoc (@arrows_coerce A B f1) (@arrows_coerce A0 B0 f2)).
exact (com_assoc (@arrows_coerce A B f1) (@arrows_coerce B C f2)).
Defined.

Coercion arrows_coerce : arrows >-> arrows_assoc.

Definition unitt_on_nodes (A : objects) (i : nodes A) : nodes A.

exact i.
Defined.

Definition bracket_left_on_nodes (A B C : objects) ( x : nodes (A /\ (B /\ C)) ) : nodes ((A /\ B) /\ C).

dependent destruction x.
exact (at_left (self (A /\ B)) C).
exact (at_left (at_left x B) C).
dependent destruction x.
exact (self ((A /\ B) /\ C)).
exact (at_left (at_right A x) C).
exact (at_right (A /\ B) x).
Defined.

Definition  bracket_right_on_nodes : forall A B C : objects, nodes ((A /\ B) /\ C) -> nodes (A /\ (B /\ C)).

  intros until C. intros x.
  dependent destruction x.
  + exact (at_right A (self (B /\ C))).
  + dependent destruction x.
  -  exact (self (A /\ (B /\ C))).
  -  exact ( at_left x (B /\ C) ).
  -  exact (at_right A (at_left x C)).
     + exact (at_right A (at_right B x)).
Defined.

Definition arrows_assoc_on_nodes : forall A B : objects, arrows_assoc A B -> nodes A -> nodes B.

  intros until B. intros f.
  induction f.
  + apply unitt_on_nodes.
  + apply bracket_left_on_nodes.
  + apply bracket_right_on_nodes.
  + { intros x.
      dependent destruction x.
      - exact (self (B /\ B0)).
      - constructor 2. revert x. exact IHf1.
      - constructor 3. revert x. exact IHf2.
    }
  + exact (fun x => IHf2 (IHf1 x)).
Defined.

Coercion arrows_assoc_on_nodes : arrows_assoc >-> Funclass.

Lemma lem001700 :
  forall A B, arrows A B -> { f : arrows_assoc A B & forall x y : A, f x <r f y -> x <r y }.

  intros until B.
  intros f.
  exists f.
  induction f. 

  - intros x y H;
    assumption.

  - dependent destruction x;
    dependent destruction y;
    intros H;
    solve [
        do 2 dependent destruction H
      | constructor
      | do 2 dependent destruction H;
        constructor;
        assumption
      | dependent destruction y;
        do 2 dependent destruction H
      | dependent destruction x;
        do 2 dependent destruction H
      | dependent destruction x;
        dependent destruction y;
        try do 2 dependent destruction H;
        repeat (constructor; try assumption) ].

  - dependent destruction x;
    dependent destruction y;
    intros H;
    solve [
        dependent destruction H
      | constructor
      | dependent destruction H;
        constructor; 
        apply IHf1;
        assumption
      | dependent destruction H;
        constructor; 
        apply IHf2;
        assumption ].

  - intros x y H; apply IHf1; apply IHf2; assumption.
Defined.

(* Print lem001700. (* 568 lines *)*)

Fixpoint object_at_node (A : objects) (x : nodes A) : objects.

Proof.
destruct x.
+ exact A.
+ exact (object_at_node A x).
+ exact (object_at_node B x).
Defined.

Compute fun p q r => object_at_node (at_right (letter r) (self (letter p /\ letter q))).


Inductive same : forall A B : objects, arrows A B -> arrows A B -> Set := 
| same_refl : forall A B f, @same A B f f
| same_trans : forall A B f g h, @same A B f g -> @same A B g h -> @same A B f h
| same_sym : forall A B f g, @same A B f g -> @same A B g f
| same_cong_com : forall A B C f f0 g g0, @same A B f f0 -> @same B C g g0 ->
 @same A C (g <o f) (g0 <o f0)
| same_cong_up_1 : forall A B A0 B0 f f0 g g0, @same A B f f0 -> @same A0 B0 g g0 ->
 @same (A /\ A0) (B /\ B0) (f /\1 g) (f0 /\1 g0)
| same_cat_left : forall A B, forall f : arrows A B, @same A B ( (unitt B) <o f ) ( f )
| same_cat_right : forall A B, forall f : arrows A B, @same A B ( f <o (unitt A)) ( f )
| same_cat_assoc : forall A B C D, forall (f : arrows A B) (g : arrows B C) (h : arrows C D), @same A D ( h <o (g <o f)  ) ( (h <o g) <o f  )
| same_bif_up_unit : forall A B, @same (A /\ B) (A /\ B) ((unitt A) /\1 (unitt B)) (unitt (A /\ B))
| same_bif_up_com : forall A B C A0 B0 C0, forall (f : arrows A B) (g : arrows B C) (f0 : arrows A0 B0) (g0 : arrows B0 C0), @same (A /\ A0) (C /\ C0) ( (g <o f) /\1 (g0 <o f0) ) ( (g /\1 g0) <o (f /\1 f0) )
| same_bracket_left_5 : forall A B C D, 
 @same (A /\ (B /\ (C /\ D))) ((((A /\ B) /\ C) /\ D))
 ( (bracket_left (A /\ B) C D) <o (bracket_left A B (C /\ D)) )
 ( (bracket_left A B C) /\1 (unitt D)  <o (bracket_left A (B /\ C) D) <o (unitt A) /\1 (bracket_left B C D) ) .


Infix "~" := (@same _ _) (at level 69). (* just before = *)
Hint Constructors same.

(**OLD NOT USED
Inductive nodes_arrows : forall A B, arrows A B -> Set :=
| self_arrows : forall A B (f : arrows A B), nodes_arrows f
| at_left_up : forall A B (f : arrows A B), nodes_arrows f -> forall A0 B0 (f0 : arrows A0 B0), nodes_arrows (f /\1 f0)
| at_right_up : forall A0 B0 (f0 : arrows A0 B0), forall A B (f : arrows A B), nodes_arrows f -> nodes_arrows (f0 /\1 f)
| at_left_com : forall B C (f : arrows B C), nodes_arrows f -> forall A (g : arrows A B), nodes_arrows (f <o g)
| at_right_com : forall B C (g : arrows B C), forall A (f : arrows A B), nodes_arrows f -> nodes_arrows (g <o f).

Hint Constructors nodes_arrows.
**)

Inductive term_bracket_left : forall A B, arrows A B -> Set :=
| term_bracket_left_self : forall A B C, term_bracket_left (bracket_left A B C)
| term_bracket_left_at_left : forall A B (f : arrows A B), term_bracket_left f -> forall A0, term_bracket_left (f /\1 (unitt A0))
| term_bracket_left_at_right : forall A, forall A0 B0 (f : arrows A0 B0), term_bracket_left f -> term_bracket_left ((unitt A) /\1 f).

Hint Constructors term_bracket_left.

(**OLD NOT USED
Fixpoint head_from_term_bracket_left (A B : objects) (f : arrows A B) (Hterm : term_bracket_left f) {struct Hterm} : nodes_arrows f.

Proof.
destruct Hterm.
- exact ( self_arrows (bracket_left A B C)).
- exact (at_left_up (head_from_term_bracket_left A B f Hterm) (unitt A0)).
- exact (at_right_up (unitt A) (head_from_term_bracket_left A0 B0 f Hterm)).
Defined.
**)

Inductive developed : forall A B, arrows A B -> Set :=
| developed_unitt : forall A, developed (unitt A)
| developed_term_bracket_left : forall A B (f : arrows A B), term_bracket_left f -> developed f
| developed_com : forall A B (f : arrows A B), developed f -> forall C (g : arrows B C), developed g -> developed (g <o f).

Hint Constructors developed.
Print Visibility.
Print prod.
Print Visibility type_scope.

Lemma lem003400 : forall A B C (f1 : arrows A B) (f2 : arrows B C), developed f1 -> developed f2 -> developed (f2 <o f1).

auto.
Defined. 
Hint Resolve lem003400.

Fixpoint length {A B : objects} (f : arrows A B) {struct f} : nat.

Proof.
destruct f.
exact 2.
exact 4.
exact (mult (length A B f1) (length A0 B0 f2)).
exact (plus (length A B f1) (length B C f2)).
Defined.

Hint Resolve mult_le_compat mult_le_compat_l mult_le_compat_r.
Lemma lem002200 : forall A B (f : arrows A B), (2 <= length f)%nat.

  induction f; simpl in *; 
    auto with zarith. 
  cut (length f1 * 2 <= length f1 * length f2)%nat;
    eauto with zarith.
Defined.
Hint Resolve lem002200.

Lemma lem003500 : forall A B (f : arrows A B), term_bracket_left f -> (4 <= length f)%nat.

  intros ? ? ? f_term_bracket_left.
  induction f_term_bracket_left; simpl in *; auto with zarith.
Defined.
Hint Resolve lem003500.


Lemma development : forall len : nat, forall A B (f : arrows A B), (length f <= len)%nat ->
{f' : arrows A B & prod (developed f') (prod (length f' <= length f)%nat (same f f'))}.

  induction len.
  - intros ? ? f ?; exfalso; assert (2 <= length f)%nat by auto; auto with zarith.
  - destruct f as [A | A B C | A1 B1 A2 B2 f1 f2 | A B C f g].
    + split with (unitt A); auto.
    + split with (bracket_left A B C); auto.
    + intros Hlen.

      (* TODO: replace useless [assert] by [cut] everywhere down, 
replace useless manual arithmetic by [fold] and [auto with zarith],
ultimately: replace all this lemma by selected [induction]/[destruct] and powerful [auto] only *)

      assert (Hlen_f1 : (length f1 <= len)%nat).
      { cut ( length f1 < S len )%nat ; [
          auto with zarith
        | ].
        cut (length f1 * 1 < length f1 * length f2)%nat ; [
            simpl in *; auto with zarith
          | ].
        cut (1 < length f2); [
            cut (0 < length f1); [
              intros; eapply mult_lt_compat_l; eauto
            | cut (2 <= length f1)%nat; auto with zarith ]
          | ].
        cut (2 <= length f2)%nat; auto with zarith. }
      pose proof ( IHlen A1 B1 f1 Hlen_f1 ) as (f1' & f1'_developed & f1'_len & f1'_same).
      clear Hlen_f1.

      assert (Hlen_f2 : (length f2 <= len)%nat).
      { cut ( length f2 < S len )%nat ; [
          auto with zarith
        | ].
        cut (1 * length f2 < length f1 * length f2)%nat ; [
            simpl in *; auto with zarith
          | ].
        cut (1 < length f1); [
            cut (0 < length f2); [
              intros; eapply mult_lt_compat_r; eauto
            | cut (2 <= length f2)%nat; auto with zarith ]
          | ].
        cut (2 <= length f1)%nat; auto with zarith. }
      pose proof ( IHlen A2 B2 f2 Hlen_f2 ) as (f2' & f2'_developed & f2'_len & f2'_same).
      clear Hlen_f2.

      destruct f1'_developed as 
          [ A1 
          | A1 B1 f1' f1'_term_bracket_left 
          | A1 B1 f1'_f f1'_f_developed C1 f1'_g f1'_g_developed ];
        destruct f2'_developed as 
          [ A2 
          | A2 B2 f2' f2'_term_bracket_left 
          | A2 B2 f2'_f f2'_f_developed C2 f2'_g f2'_g_developed].

      * (* unitt /\ unitt *)
        split with (unitt (A1 /\ A2)); simpl in *; repeat split; cut (length f1 * 2 <= length f1 * length f2)%nat;eauto with zarith.
      * (* unitt /\ termbracket *)
        split with ((unitt A1) /\1 f2'); repeat split; [
          auto 
        | simpl; fold (2 * (length f2')); auto with zarith
        | auto ].
      * (* unitt A1 /\ (f2'_g <o f2_f) *)
        assert (Hlen_f'_g : (length (unitt A1 /\1 f2'_g) <=  len)%nat).
        { assert (length f2'_g < length f2)%nat by (assert (2 <= length f2'_f)%nat; simpl in *; auto with zarith).
          assert (length f1 * length f2'_g < length f1 * length f2)%nat by (eapply mult_lt_compat_l; cut (2 <= length f1)%nat; auto with zarith).
          assert (length (unitt A1 /\1 f2'_g) <= length f1 * length f2'_g)%nat by (simpl in *; fold (2 * length f2'_g)%nat; eapply mult_le_compat_r; eauto).
          simpl in *; auto with zarith. }
        pose proof (IHlen (A1 /\ B2) (A1 /\ C2) (unitt A1 /\1 f2'_g) Hlen_f'_g) as (f'_g & f'_g_developed & f'_g_len & f'_g_same).

        assert (Hlen_f'_f : (length (unitt A1 /\1 f2'_f) <=  len)%nat).
        { assert (length f2'_f < length f2)%nat by (assert (2 <= length f2'_g)%nat; simpl in *; auto with zarith).
          assert (length f1 * length f2'_f < length f1 * length f2)%nat by (eapply mult_lt_compat_l; cut (2 <= length f1)%nat; auto with zarith).
          assert (length (unitt A1 /\1 f2'_f) <= length f1 * length f2'_f)%nat by (simpl in *; fold (2 * length f2'_f)%nat; eapply mult_le_compat_r; eauto).
          simpl in *; auto with zarith. }
        pose proof (IHlen (A1 /\ A2) (A1 /\ B2) (unitt A1 /\1 f2'_f) Hlen_f'_f) as (f'_f & f'_f_developed & f'_f_len & f'_f_same).

       { split with ( f'_g <o f'_f ); repeat split.
         - auto.
         - assert (2 <= length f1)%nat by auto.
           simpl in *;
             fold (2 * length f2'_f) in *;
             fold (2 * length f2'_g) in *.
           assert (length f'_f + length f'_g <= 2 * length f2'_f + 2 * length f2'_g)%nat by auto with zarith.
           assert (2 * length f2'_f + 2 * length f2'_g <= 2 * (length f2'_f + length f2'_g))%nat by auto with zarith.
           assert (2 * (length f2'_f + length f2'_g) <= 2 * length f2)%nat by (eapply mult_le_compat_l; eauto).
           assert (2 * length f2 <= length f1 * length f2)%nat by (eapply mult_le_compat_r; eauto).
           auto with zarith.
         - assert (same (f1 /\1 f2) ((unitt A1) /\1 (f2'_g <o f2'_f))) by auto.
           assert (same ( (unitt A1) /\1 (f2'_g <o f2'_f) ) ((unitt A1 /\1 f2'_g) <o  (unitt A1 /\1 f2'_f) ) ) by eauto.
           assert (same (unitt A1 /\1 f2'_g <o unitt A1 /\1 f2'_f) (f'_g <o f'_f)) by auto.
           eauto. }

      * (* termbracket f1' /\ unitt A2 *)
        split with ( f1' /\1 (unitt A2) ); repeat split; [
          auto 
        | simpl; fold (2 * (length f1')); auto with zarith
        | auto ].

      * (* termbracket f1' /\ termbracket f2' *)
        assert ( Hlen_f'_g : (length (f1' /\1 (unitt A2)) <= len)%nat ).
        { simpl in *; fold (length f1' * 2).
          assert (length f1' * 2 < length f1' * length f2)%nat by (assert (4 <= length f2')%nat by auto; assert (2 < length f2)%nat by auto with zarith; eapply mult_lt_compat_l; cut (2 <= length f1')%nat; auto with zarith).
          assert (length f1' * length f2 <= length f1 * length f2)%nat by (eapply mult_le_compat_r; eauto).
          auto with zarith. }
        pose proof (IHlen _ _ (f1' /\1 (unitt A2)) Hlen_f'_g) as (f'_g & f'_g_developed & f'_g_len & f'_g_same).
        Guarded.
        
        assert ( Hlen_f'_f : (length ( (unitt B1) /\1 f2' ) <= len)%nat ).
        { simpl in *; fold (2 * length f2').
          assert (2 * length f2' < length f1 * length f2')%nat by (assert (4 <= length f1')%nat by auto; assert (2 < length f1)%nat by auto with zarith; eapply mult_lt_compat_r; cut (2 <= length f2')%nat; auto with zarith).
          assert (length f1 * length f2' <= length f1 * length f2)%nat by (eapply mult_le_compat_l; eauto).
          auto with zarith. }
        pose proof (IHlen _ _ ((unitt B1) /\1 f2') Hlen_f'_f) as (f'_f & f'_f_developed & f'_f_len & f'_f_same).

        { split with (f'_f <o f'_g); repeat split.
          - auto.
          - simpl in *; fold (2 *(length f2'))%nat in *; fold (length f1' * 2) in *.
            assert (4 <= length f1')%nat by auto; assert (4 <= length f2')%nat by auto.
            refine (match le_ge_dec (length f1') (length f2') with
                      | left Hlen_f1'_less_f2' => _
                      | right Hlen_f2'_less_f1' => _
                    end).
            + SearchPattern (_ <= mult _ _)%nat.
              assert (length f'_g + length f'_f <= 4 * length f2')%nat by auto with zarith.
              assert (4 * length f2' <= length f1' * length f2')%nat by auto with zarith.
              assert (length f1' * length f2' <= length f1 * length f2)%nat by auto with zarith.
              auto with zarith.
            + assert (length f'_g + length f'_f <= length f1' * 4)%nat by auto with zarith.
              assert (length f1' * 4 <= length f1' * length f2')%nat by auto with zarith.
              assert (length f1' * length f2' <= length f1 * length f2)%nat by auto with zarith.
              auto with zarith.
          - assert (same (f1 /\1 f2) (f1' /\1 f2')) by auto.
            assert (same (f1') (unitt _ <o f1')) by auto.
            assert (same (f2') (f2' <o unitt _)) by auto.
            assert (same (f1' /\1 f2') ( (unitt B1 /\1 f2') <o (f1' /\1 unitt A2) ) ) by eauto.
            eauto. }

      * (* term_brac f1' /\ (dev f2'_g <o dev f2'_f) *)
        assert (Hlen_f'_f : (length (f1' /\1 f2'_f) <= len)%nat).
        { assert (length f2'_f < length (f2'_g <o f2'_f))%nat by (assert (2 <= length f2'_g)%nat by auto; simpl; auto with zarith).          
          assert (length f2'_f < length f2) by auto with zarith.
          simpl in *.
          assert (0 < length f1')%nat by (assert (2 <= length f1')%nat by auto; auto with zarith).
          assert (length f1' * length f2'_f < length f1' * length f2)%nat by (eapply mult_lt_compat_l; auto).
          assert (length f1' * length f2 <= length f1 * length f2)%nat by auto with zarith.
          auto with zarith. }
        pose proof (IHlen _ _ (f1' /\1 f2'_f) Hlen_f'_f) as (f'_f & f'_f_developed & f'_f_len & f'_f_same).

        assert (Hlen_f'_g : (length (unitt B1 /\1 f2'_g) <= len)%nat).
        { assert (length f2'_g < length (f2'_g <o f2'_f))%nat by (assert (2 <= length f2'_f)%nat by auto; simpl; auto with zarith).
          assert (length f2'_g < length f2) by auto with zarith.
          simpl in *; fold (2 * length f2'_g).
          assert (2 <= length f1)%nat by auto.
          assert (2 * length f2'_g < 2 * length f2) by auto with zarith.
          assert (2 * length f2 <= length f1 * length f2)%nat by auto with zarith.
          auto with zarith. }
        pose proof (IHlen _ _ (unitt B1 /\1 f2'_g) Hlen_f'_g) as (f'_g & f'_g_developed & f'_g_len & f'_g_same).

        { split with ( f'_g <o f'_f ); repeat split.
          - auto.
          - simpl in *; fold (2 * length f2'_g) in *.
            assert (2 <= length f1')%nat by auto.
            assert (length f'_f + length f'_g <= length f1' * length f2'_f + 2 * length f2'_g)% nat by auto with zarith.
            assert ( 2 * length f2'_g <=  length f1' * length f2'_g)%nat by auto with zarith.
            assert (length f1' * length f2'_f + 2 * length f2'_g <= length f1' * length f2'_f +  length f1' * length f2'_g)%nat by auto with zarith.
SearchPattern (_ * (_ + _) = _)%nat.
            assert (length f1' * length f2'_f +  length f1' * length f2'_g = length f1' * (length f2'_f +  length f2'_g))%nat by (symmetry; apply mult_plus_distr_l).
            assert (length f1' * (length f2'_f + length f2'_g) <= length f1' * length f2)%nat by auto with zarith.
            assert (length f1' * length f2 <= length f1 * length f2)%nat by auto with zarith.
            auto with zarith.
          - assert (same f1' (unitt _ <o f1')) by auto.
            assert (same (f1 /\1 f2) (f1' /\1 (f2'_g <o f2'_f))) by auto.
            assert (same (f1' /\1 (f2'_g <o f2'_f)) ((unitt B1 <o f1') /\1 (f2'_g <o f2'_f))) by auto.
            assert (same (((unitt B1 <o f1') /\1 (f2'_g <o f2'_f))) ( (unitt B1 /\1 f2'_g) <o (f1' /\1 f2'_f) )) by auto.
            eauto. }
        Guarded.

      * (* ( dev f1'_g <o dev f1'_f ) /\ unitt A2 *)
        assert (Hlen_f'_f : (length (f1'_f /\1 unitt A2) <= len)%nat).
        { cut (length f1'_f * length f2 < S len)%nat; [
            cut (length (f1'_f /\1 unitt A2) <= length f1'_f * length f2)%nat;
            simpl in *; auto with zarith
          |  ].
          cut (length f1'_f * length f2 < length f1 * length f2); [
              simpl in *; auto with zarith
            | ].          
          cut (length f1'_f < length f1)%nat; [
              cut (2 <= length f2)%nat; [
                intros; apply mult_lt_compat_r; auto with zarith
              | auto ]
            | ].
          cut (2 <= length f1'_g)%nat; simpl in *; auto with zarith. }
        pose proof (IHlen _ _ (f1'_f /\1 unitt A2) Hlen_f'_f) as (f'_f & f'_f_developed & f'_f_len & f'_f_same).

        assert (Hlen_f'_g : (length (f1'_g /\1 unitt A2) <= len)%nat).
        { cut (length f1'_g * length f2 < S len)%nat; [
            cut (length (f1'_g /\1 unitt A2) <= length f1'_g * length f2)%nat;
            simpl in *; auto with zarith
          |  ].
          cut (length f1'_g * length f2 < length f1 * length f2); [
              simpl in *; auto with zarith
            | ].
          cut (length f1'_g < length f1)%nat; [
              cut (2 <= length f2)%nat; [
                intros; apply mult_lt_compat_r; auto with zarith
              | auto ]
            | ].
          cut (2 <= length f1'_f)%nat; simpl in *; auto with zarith. }
        pose proof (IHlen _ _ (f1'_g /\1 unitt A2) Hlen_f'_g) as (f'_g & f'_g_developed & f'_g_len & f'_g_same).

       { split with ( f'_g <o f'_f ); repeat split.
         - (*|- developed (f'_g <o f'_f) *)
           auto.
         - (*|- length f'_f + length f'_g <= length f1 * length f2 *)
           simpl in * ; fold (length f1'_f * 2) in *; fold (length f1'_g * 2) in *.
           
           cut ( length f1'_f * 2 + length f1'_g * 2 <= length f1 * length f2 )%nat ; [
               cut ( length f'_f + length f'_g <= length f1'_f * 2 + length f1'_g * 2 )%nat ;
                 auto with zarith
             | ].
           cut ( (length f1'_f + length f1'_g) * 2 <= length f1 * length f2 )%nat ; [
               cut ( length f1'_f * 2 + length f1'_g * 2 <= (length f1'_f + length f1'_g) * 2 )%nat ;
               auto with zarith
             | ].
           auto with zarith.
         - (*|- (f1 /\1 f2) ~ (f'_g <o f'_f) *)
           cut (same ((f1'_g <o f1'_f) /\1 unitt A2) (f'_g <o f'_f)); [
             cut (same (f1 /\1 f2) ((f1'_g <o f1'_f) /\1 unitt A2)); eauto
           | ].
           cut (same ((f1'_g /\1 unitt A2) <o (f1'_f /\1 unitt A2)) (f'_g <o f'_f)); [
               cut (same ((f1'_g <o f1'_f) /\1 unitt A2) ((f1'_g /\1 unitt A2) <o (f1'_f /\1 unitt A2))); eauto
             | ].
           eauto. }

      * (* (dev f1'_g <o dev f1'_f) /\ term_bra f2'
           ~ (f1'_g /\ unitt) <o (f1'_f /\ f2') *)
        assert (Hlen_f'_f : (length (f1'_f /\1 f2') <= len)%nat).
        { cut ((length f1'_f + length f1'_g) * length f2' <= S len)%nat ;[
            cut (length f1'_f * length f2' < (length f1'_f + length f1'_g) * length f2')%nat ;[
            simpl; auto with zarith

            | cut (2 <= length f1'_g)%nat ;[
                cut (2 <= length f2')%nat ;[
                  intros; eapply mult_lt_compat_r; eauto with zarith
                | auto]
              | auto]
            ]
          | ].
          cut ((length f1'_f + length f1'_g) * length f2' <=  length (f1 /\1 f2))%nat ;[
              auto with zarith
            | simpl in *; auto with zarith ]. }
        pose proof (IHlen _ _ (f1'_f /\1 f2') Hlen_f'_f) as (f'_f & f'_f_developed & f'_f_len & f'_f_same).

        assert (Hlen_f'_g : (length (f1'_g /\1 unitt B2) <= len)%nat).
        { cut ((length f1'_f + length f1'_g) * length (unitt B2) <= S len)%nat ;[
            cut (length f1'_g * length (unitt B2) < (length f1'_f + length f1'_g) * length (unitt B2))%nat ;[
              simpl; auto with zarith

            | cut (2 <= length f1'_f)%nat ;[
                cut (2 <= length (unitt B2))%nat ;[
                  intros; eapply mult_lt_compat_r; eauto with zarith
                | auto]
              | auto]
            ]
          | ].
          cut ((length f1'_f + length f1'_g) * length (unitt B2) <=  length (f1 /\1 f2))%nat ;[
              auto with zarith
            | simpl in *; auto with zarith ]. }
        pose proof (IHlen _ _ (f1'_g /\1 unitt B2) Hlen_f'_g) as (f'_g & f'_g_developed & f'_g_len & f'_g_same).

        { split with ( f'_g <o f'_f ); repeat split.
          - (*|-  developed (f'_g <o f'_f) *)
            auto.
          - (*|- length (f'_g <o f'_f) <= length (f1 /\1 f2) *)
            cut (length (f1'_f /\1 f2') + length (f1'_g /\1 unitt B2) <= length (f1 /\1 f2))%nat ;[
              cut (length (f'_g <o f'_f) <= length (f1'_f /\1 f2') + length (f1'_g /\1 unitt B2))%nat ;[
               auto with zarith
              | simpl in *; auto with zarith ]
            | ].
            cut (length f1'_f * length f2' + length f1'_g * length f2' <= length (f1 /\1 f2))%nat ;[
                cut (length (f1'_f /\1 f2') + length (f1'_g /\1 unitt B2) <= length f1'_f * length f2' + length f1'_g * length f2')%nat ;[
                  auto with zarith
                | cut (length f1'_g * 2 <= length f1'_g * length f2')%nat ;[
                    simpl; auto with zarith
                  | cut (2 <= length f2')%nat;
                    auto with zarith ]
                ]
              | ].
            cut ((length f1'_f + length f1'_g) * length f2' <= length (f1 /\1 f2))%nat ;[
                cut ((length f1'_f * length f2' + length f1'_g * length f2' = (length f1'_f + length f1'_g) * length f2'))%nat ;[
                  auto with zarith 
                | (*??*) symmetry; apply mult_plus_distr_r]
              | ].
            simpl in *; auto with zarith.
          - (*  (f1 /\1 f2) ~ (f'_g <o f'_f) *)
            cut (same ((f1'_g <o f1'_f) /\1 f2') (f'_g <o f'_f)) ;[
              eauto
            | ].
            cut (same ((f1'_g <o f1'_f) /\1 (unitt B2 <o f2')) (f'_g <o f'_f)) ;[
                cut (same f2' (unitt B2 <o f2')) ;
                  eauto
              | ].
            cut (same ((f1'_g /\1 unitt B2) <o (f1'_f /\1 f2')) (f'_g <o f'_f)) ;[
                eauto
              | ].
            auto. }

        * (* ( dev f1'_g <o dev f1'_f ) /\ ( dev f2'_g <o dev f2'_f )
           ~ ( f1'_g /\ f2'_g ) <o ( f1'_f /\ f2'_f ) *)

          assert (Hlen_f'_f : (length (f1'_f /\1 f2'_f) <= len)%nat).
          { cut (length (f1'_g <o f1'_f) * length (f2'_g <o f2'_f) <= S len)%nat ;[
              cut (length (f1'_f /\1 f2'_f) < length (f1'_g <o f1'_f) * length (f2'_g <o f2'_f))%nat ;[
                auto with zarith
              | cut (length f1'_f < length (f1'_g <o f1'_f))%nat ;[
                  cut (length f2'_f < length (f2'_g <o f2'_f))%nat ;[
                    simpl in *; intros; 
                    transitivity ((length f1'_f + length f1'_g) * length f2'_f)%nat; [eapply mult_lt_compat_r;
                                                                                       cut (2 <= length f2'_f)%nat;
                                                                                       auto with zarith
                                                                                     | eapply mult_lt_compat_l;
                                                                                       auto with zarith ]
                  | cut (2 <= length f2'_g)%nat; simpl in *; auto with zarith ]
                | cut (2 <= length f1'_g)%nat; simpl in *; auto with zarith ]
              ]
            | ].
            cut (length f1 * length f2 <= S len)%nat;
              cut (length (f1'_g <o f1'_f) * length (f2'_g <o f2'_f) <= length f1 * length f2)%nat;              
              simpl in *; auto with zarith. }
          pose proof (IHlen _ _ (f1'_f /\1 f2'_f) Hlen_f'_f) as (f'_f & f'_f_developed & f'_f_len & f'_f_same).

          assert (Hlen_f'_g : (length (f1'_g /\1 f2'_g) <= len)%nat).
          { cut (length (f1'_g <o f1'_f) * length (f2'_g <o f2'_f) <= S len)%nat ;[
              cut (length (f1'_g /\1 f2'_g) < length (f1'_g <o f1'_f) * length (f2'_g <o f2'_f))%nat ;[
                auto with zarith
              | cut (length f1'_g < length (f1'_g <o f1'_f))%nat ;[
                  cut (length f2'_g < length (f2'_g <o f2'_f))%nat ;[
                    simpl in *; intros; 
                    transitivity ((length f1'_f + length f1'_g) * length f2'_g)%nat; [eapply mult_lt_compat_r;
                                                                                       cut (2 <= length f2'_g)%nat;
                                                                                       auto with zarith
                                                                                     | eapply mult_lt_compat_l;
                                                                                       auto with zarith ]
                  | cut (2 <= length f2'_f)%nat; simpl in *; auto with zarith ]
                | cut (2 <= length f1'_f)%nat; simpl in *; auto with zarith ]
              ]
            | ].
            cut (length f1 * length f2 <= S len)%nat;
              cut (length (f1'_g <o f1'_f) * length (f2'_g <o f2'_f) <= length f1 * length f2)%nat;              
              simpl in *; auto with zarith. }
          pose proof (IHlen _ _ (f1'_g /\1 f2'_g) Hlen_f'_g) as (f'_g & f'_g_developed & f'_g_len & f'_g_same).
          
        { split with ( f'_g <o f'_f ); repeat split.
          - (*|-  developed (f'_g <o f'_f) *)
            auto.
          - (*|- length (f'_g <o f'_f) <= length (f1 /\1 f2) *)
            cut (length (f1'_f /\1 f2'_f) + length (f1'_g /\1 f2'_g) <= length (f1 /\1 f2))%nat ;[
              cut (length (f'_g <o f'_f) <= length (f1'_f /\1 f2'_f) + length (f1'_g /\1 f2'_g))%nat;
              simpl in *; auto with zarith
            | ].
            cut (length (f1'_g <o f1'_f) * length (f2'_g <o f2'_f) <= length (f1 /\1 f2))%nat ;[
                cut (length (f1'_f /\1 f2'_f) + length (f1'_g /\1 f2'_g) <= length (f1'_g <o f1'_f) * length (f2'_g <o f2'_f))%nat ;[
                  auto with zarith
                | simpl;
                  rewrite  mult_plus_distr_l;
                  rewrite 2 mult_plus_distr_r;
                  generalize  (length f1'_f * length f2'_f)%nat , (length f1'_g * length f2'_g)%nat, (length f1'_g * length f2'_f)%nat , (length f1'_f * length f2'_g)%nat;
                  auto with zarith
                ]
              | ].
            simpl in *; auto with zarith.
          - (*|- (f1 /\1 f2) ~ (f'_g <o f'_f) *)
            eauto (* >:D *). }

    + (* g <o f *)
      intros Hlen. 
      assert (Hlen_f : (length f <= len)%nat).
      { cut (2 <= length g)%nat;
        simpl in *; auto with zarith. }
      pose proof (IHlen _ _ f Hlen_f) as (f'_f & f'_f_developed & f'_f_len & f'_f_same).
      
      assert (Hlen_g : (length g <= len)%nat).
      { cut (2 <= length f)%nat;
        simpl in *; auto with zarith. }
      pose proof (IHlen _ _ g Hlen_g) as (f'_g & f'_g_developed & f'_g_len & f'_g_same).
           
        { split with ( f'_g <o f'_f ); repeat split.
          - (*|-  developed (f'_g <o f'_f) *)
            auto.
          - (*|- length (f'_g <o f'_f) <= length (g /\1 f) *)
            simpl in *; auto with zarith.
          - (*|- (g <o f) ~ (f'_g <o f'_f) *)
            eauto. }
        Guarded.
Defined.
(*Print development.*)
(** before doing [Recursive Extraction development.], one shall erase all the logical [Set] occurrences and replace them with [Prop]**)
(*Recursive Extraction development.*)


(**OLD NOT USED
Check nodes_arrows.
Fixpoint arrow_at_node A B (f : arrows A B) (x : nodes_arrows f) : {U:_ & {V:_ & arrows U V}}.

Proof.
destruct x.
+ split with A; split with B; exact f.
+ exact (arrow_at_node A B f x).
+ exact (arrow_at_node A B f x).
+ exact (arrow_at_node B C f x).
+ exact (arrow_at_node A B f x).
Defined.

Compute fun A B C => let ' (existT U (existT V g)) := arrow_at_node (at_right_com (unitt (A /\ ((A /\ B) /\ C))) (at_right_up (unitt A) (self_arrows (bracket_left A B C)))) in (existT (fun U => {V : objects & arrows U V}) U (existT _ V g)).
Compute fun A B C => arrow_at_node (at_right_com (unitt (A /\ ((A /\ B) /\ C))) (at_right_up (unitt A) (self_arrows (bracket_left A B C)))).
**)

Lemma lem001700' :
  forall A B (f : arrows A B), forall x y : A, f x <r f y -> x <r y.

  induction f. 

  - intros x y H;
    assumption.

  - dependent destruction x;
    dependent destruction y;
    intros H;
    solve [
        do 2 dependent destruction H
      | constructor
      | do 2 dependent destruction H;
        constructor;
        assumption
      | dependent destruction y;
        do 2 dependent destruction H
      | dependent destruction x;
        do 2 dependent destruction H
      | dependent destruction x;
        dependent destruction y;
        try do 2 dependent destruction H;
        repeat (constructor; try assumption) ].

  - dependent destruction x;
    dependent destruction y;
    intros H;
    solve [
        dependent destruction H
      | constructor
      | dependent destruction H;
        constructor; 
        apply IHf1;
        assumption
      | dependent destruction H;
        constructor; 
        apply IHf2;
        assumption ].

  - intros x y H; apply IHf1; apply IHf2; assumption.
Defined.
Hint Resolve lem001700'.

Lemma lem001700'' :
  forall A B, arrows A B -> { f : arrows_assoc A B & forall x y : A, f x <r f y -> x <r y }.

  intros A B f.
  split with f.
  apply lem001700'.
Defined.
Hint Resolve lem001700''.

Fixpoint rev A B (f : arrows_assoc A B) : arrows_assoc B A.

Proof.
destruct f as [ A | A B C | A B C | A B A0 B0 f f0 | A B C f g ].
- exact (unitt A).
- exact (bracket_right_assoc A B C).
- exact (bracket_left_assoc A B C).
- exact (up_1_assoc (rev A B f) (rev A0 B0 f0)).
- exact (com_assoc (rev B C g) (rev A B f)).
Defined.

Lemma lem004000 : forall A B (f : arrows_assoc A B), forall x : A, (com_assoc f (rev f)) x = x.

  induction f.
  - reflexivity. 
  - dependent destruction x. 
    * reflexivity.
    * reflexivity.
    * dependent destruction x; reflexivity.
  - dependent destruction x. 
    * reflexivity.
    * dependent destruction x; reflexivity.
    * reflexivity.
  - dependent destruction x.
    * reflexivity.
    * simpl arrows_assoc_on_nodes.
      replace (at_left x A0) with (at_left ((com_assoc f1 (rev f1)) x) A0) by (rewrite IHf1; reflexivity).
      reflexivity.
    * simpl arrows_assoc_on_nodes.
      replace (at_right A x) with (at_right A ((com_assoc f2 (rev f2)) x)) by (rewrite IHf2; reflexivity).
      reflexivity.
  -  intros x. simpl in *. rewrite IHf2. rewrite IHf1. reflexivity.
Defined.
Hint Resolve lem004000.

Lemma lem004100 : forall A B (f : arrows_assoc A B), (rev (rev f)) = f.

  induction f as [ | | | A B A0 B0 f1 IHf1 f2 IHf2 | A B C f1 IHf1 f2 IHf2 ];
  simpl; try rewrite IHf1, IHf2; reflexivity.
Defined.
Hint Resolve lem004100.

Lemma lem004200 : forall A B (f : arrows_assoc A B), forall x : B, (com_assoc (rev f) f) x = x.

  intros A B f.
  replace (com_assoc (rev f) f) with (com_assoc (rev f) (rev (rev f))).
  - generalize (rev f); auto.
  - replace (rev (rev f)) with f by auto; reflexivity.
Defined.
Hint Resolve lem004200.

Lemma lem004300 : forall A B (f : arrows_assoc A B), forall x : A, ((rev f) (f x)) = x.

intros until x;
replace ((rev f) (f x)) with ((com_assoc f (rev f)) x) by reflexivity;
auto.
Defined.
Hint Resolve lem004300.

Lemma lem004400 : forall A B (f : arrows_assoc A B), forall x : B, f ((rev f) x) = x.

intros until x;
replace (f ((rev f) x)) with ((com_assoc (rev f) f) x) by reflexivity;
auto.
Defined.
Hint Resolve lem004400.


Inductive bracket_left_occurs_in : forall A B, arrows A B -> Set :=
| bracket_left_occurs_in_self : forall A B C, bracket_left_occurs_in (bracket_left A B C)
| bracket_left_occurs_in_up_left : forall A B A0 B0 (f : arrows A B) (f0 : arrows A0 B0), bracket_left_occurs_in f -> bracket_left_occurs_in (f /\1 f0)
| bracket_left_occurs_in_up_right : forall A0 B0 A B (f0 : arrows A0 B0) (f : arrows A B), bracket_left_occurs_in f -> bracket_left_occurs_in (f0 /\1 f)
| bracket_left_occurs_in_com_left : forall B C (f : arrows B C), bracket_left_occurs_in f -> forall A (g : arrows A B), bracket_left_occurs_in (f <o g)
| bracket_left_occurs_in_com_right : forall B C (g : arrows B C), forall A (f : arrows A B), bracket_left_occurs_in f -> bracket_left_occurs_in (g <o f).
Hint Constructors bracket_left_occurs_in.

Lemma lem004500 :
  forall A B (f : arrows A B),
    bracket_left_occurs_in f
    -> {x: A & {y : A & prod (x <r y) (f x <r f y -> Empty_set)}}.

  induction 1 as [ A B C 
                 | A B A0 B0 f f0 f_bracket_left_occurs_in 
                 | A0 B0 A B f0 f f_bracket_left_occurs_in 
                 | B C f f_bracket_left_occurs_in IHf_bracket_left_occurs_in A g 
                 | B C g A f f_bracket_left_occurs_in IHf_bracket_left_occurs_in ].

  - split with (self (A /\ (B /\ C))).
    split with (at_right A (self (B /\ C))).
    split; [auto | intro H_ltr_f; dependent destruction H_ltr_f ].

  - destruct IHf_bracket_left_occurs_in as (x & y & IH_ltr & IH_ltr_f).
    split with (at_left x A0); split with (at_left y A0);
    split; [auto | intro H_ltr_up_f_f0; dependent destruction H_ltr_up_f_f0; auto].

  - destruct IHf_bracket_left_occurs_in as (x & y & IH_ltr & IH_ltr_f).
    split with (at_right A0 x); split with (at_right A0 y);
    split; [auto | intro H_ltr_up_f0_f; dependent destruction H_ltr_up_f0_f; auto].

  - destruct IHf_bracket_left_occurs_in as (x & y & IH_ltr & IH_ltr_f).
    split with ((rev g) x);  split with ((rev g) y); split.
    + replace x with (g ((rev g) x)) in IH_ltr by auto.
      replace y with (g ((rev g) y)) in IH_ltr by auto.
      eauto.
    + replace x with (g ((rev g) x)) in IH_ltr_f by auto.
      replace y with (g ((rev g) y)) in IH_ltr_f by auto.
      auto.
  - destruct IHf_bracket_left_occurs_in as (x & y & IH_ltr & IH_ltr_f).
    split with x; split with y; split.
    + assumption.
    + cut ((g <o f) x <r (g <o f) y -> f x <r f y); [
        auto
      | ].
      simpl; eauto.
Defined.
Hint Resolve lem004500.


Inductive bracket_left_not_occurs_in : forall A B, arrows A B -> Set :=
| bracket_left_not_occurs_in_unitt : forall A, bracket_left_not_occurs_in (unitt A)
| bracket_left_not_occurs_in_up : forall A B A0 B0 (f : arrows A B) (f0 : arrows A0 B0), bracket_left_not_occurs_in f -> bracket_left_not_occurs_in f0 -> bracket_left_not_occurs_in (f /\1 f0)
| bracket_left_not_occurs_in_com : forall A B C (f : arrows A B) (g : arrows B C), bracket_left_not_occurs_in f -> bracket_left_not_occurs_in g -> bracket_left_not_occurs_in (g <o f).
Hint Constructors bracket_left_not_occurs_in.

Lemma lem004600 : forall A B (f: arrows A B), bracket_left_not_occurs_in f -> bracket_left_occurs_in f -> Empty_set.

  induction f.
  - intros f_bracket_left_not_occurs_in f_bracket_left_occurs_in.
    inversion f_bracket_left_occurs_in.
  - intros f_bracket_left_not_occurs_in.
    inversion f_bracket_left_not_occurs_in.
  - intros f_bracket_left_not_occurs_in.
    dependent destruction f_bracket_left_not_occurs_in.
    intros f_bracket_left_occurs_in.
    dependent destruction f_bracket_left_occurs_in; auto.
  - intros f_bracket_left_not_occurs_in.
    dependent destruction f_bracket_left_not_occurs_in.
    intros f_bracket_left_occurs_in.
    dependent destruction f_bracket_left_occurs_in; auto.
Defined.
Hint Resolve lem004600.

Lemma lem004700 : forall A B (f: arrows A B), (bracket_left_occurs_in f -> Empty_set) -> bracket_left_not_occurs_in f.
  
  induction f.
  - auto.
  - intros not_f_bracket_left_occurs_in. elimtype Empty_set. auto.
  - auto.
  - auto.
Defined.
Hint Resolve lem004700.

Lemma lem004800 : forall A B (f : arrows A B), (bracket_left_occurs_in f -> Empty_set) -> forall x y : A, x <r y -> f x <r f y.

  intros A B f H.
  assert (f_bracket_left_not_occurs_in : bracket_left_not_occurs_in f) by auto;
    clear H.
  dependent induction f_bracket_left_not_occurs_in.
  - auto.
  - intros x y H_ltr.
    dependent destruction H_ltr.
    + constructor.
    + constructor; auto.
    + constructor; auto.
  - intros x y H_ltr. 
    replace ((g <o f) x) with (g (f x)) by auto.
    replace ((g <o f) y) with (g (f y)) by auto.
    auto.
Defined.
Hint Resolve lem004800.


(* begin extraction lemma *)

(*

bracket_left

A /\ (B /\ C)

(A /\ B) /\ C

==

multi_bracket_left

A /\ ((B /\ C) /\ D)

(A /\ (B /\ C)) /\ D

((A /\ B) /\ C) /\ D

==

term_bracket_left <: nodal_arrow

(X /\ (A /\ (B /\ C))) /\ Y

(X /\ ((A /\ B) /\ C)) /\ Y

==

goal:
term_multi_bracket_left <: nodal_arrow

(X /\ A /\ ((B /\ C) /\ D)) /\ Y

(X /\ (A /\ (B /\ C)) /\ D) /\ Y

(X /\ ((A /\ B) /\ C) /\ D) /\ Y

==

nodal_arrow

nodal_arrow : (A : object)(x : A)(Y : object)(f : arrow (object_at_node x) Y), { B : objects & { f' : arrow A B & object_at_node (f' x) = Y : Prop (*opt*) * f' restr x = f : Prop } }

*)


Fixpoint foldright (A : objects) (Dlist : list objects) : objects.

Proof.
  destruct Dlist as [ | D0 Dlist].
  - exact A.
  - exact ((foldright A Dlist) /\ D0).
Defined.

Infix "/\\" := foldright (at level 80, right associativity) . (*  *)

Fixpoint multi_bracket_left_specif
  (A B C : objects) (Dlist : list objects)
: { f : arrows (A /\ ((B /\ C) /\\ Dlist)) (((A /\ B) /\ C) /\\ Dlist) & 
               forall x y : nodes (A /\ ((B /\ C) /\\ Dlist)),
                 ( x = self _ -> Empty_set) -> x <r y -> f x <r f y }.
Proof.
  destruct Dlist as [ | D0 Dlist].

  - split with (bracket_left A B C).
    intros x y H_x_is_self H_ltr.
    simpl in * |- .
    dependent destruction H_ltr.
    + elimtype Empty_set; auto.
    + constructor; auto.
    + dependent destruction H_ltr;
      constructor; auto.

  - simpl. 
    split with ( ( (projT1( multi_bracket_left_specif A B C Dlist )) /\1 unitt _) <o (bracket_left A (foldright (B /\ C) Dlist) D0) ).
    intros x y H_x_is_self H_ltr.
    dependent destruction H_ltr.
    + elimtype Empty_set; auto.
    + constructor.
      eapply  (projT2 ( multi_bracket_left_specif A B C Dlist )).
      * discriminate.
      * constructor; auto.
    + dependent destruction H_ltr;
      solve [
          constructor; auto
        | constructor; 
          eapply (projT2 ( multi_bracket_left_specif A B C Dlist )); [
            discriminate 
          | constructor;
            auto
          ] 
        ].
Defined.

Definition multi_bracket_left
  (A B C : objects) (Dlist : list objects)
: arrows (A /\ foldright (B /\ C) Dlist) (foldright ((A /\ B) /\ C) Dlist).

exact (projT1 (multi_bracket_left_specif A B C Dlist)).
(*destruct (multi_bracket_left_specif A B C Dlist) as (multi_bracket_left_specif_f & multi_bracket_left_specif_prop).
exact multi_bracket_left_specif_f.*)
Defined.
Hint Resolve multi_bracket_left.
Hint Unfold multi_bracket_left.

Definition multi_bracket_left_prop
  (A B C : objects) (Dlist : list objects)
  : forall x y : nodes (A /\ ((B /\ C) /\\ Dlist)),
      ( x = self _ -> Empty_set) -> x <r y -> (multi_bracket_left A B C Dlist) x <r (multi_bracket_left A B C Dlist) y  .

exact (projT2 ( multi_bracket_left_specif A B C Dlist)).
Defined.
Hint Resolve multi_bracket_left_prop.
Hint Unfold multi_bracket_left_prop.

(*
Fixpoint multi_bracket_left
  (A B C : objects) (Dlist : list objects)
: arrows (A /\ foldright (B /\ C) Dlist) (foldright ((A /\ B) /\ C) Dlist).

Proof.
  destruct Dlist as [ | D0 Dlist].
  - exact (bracket_left A B C).
  - simpl. 
    cut ( arrows (A /\ foldright (B /\ C) Dlist)
                 (foldright ((A /\ B) /\ C) Dlist) ) ; [
        intros IHmulti_bracket_left;
        cut ( arrows (A /\ (foldright (B /\ C) Dlist /\ D0))
                     ((A /\ foldright (B /\ C) Dlist) /\ D0) ); [
          intros top_bracket_left;
          exact ( (IHmulti_bracket_left /\1 unitt _) <o top_bracket_left )
        | exact (bracket_left A (foldright (B /\ C) Dlist) D0) ]

      | exact ( multi_bracket_left A B C Dlist ) ].
Defined.
*)

Inductive term_multi_bracket_left : forall A B, arrows A B -> Set :=
| term_multi_bracket_left_self : forall A B C Dlist, term_multi_bracket_left (multi_bracket_left A B C Dlist)
| term_multi_bracket_left_at_left : forall A B (f : arrows A B), term_multi_bracket_left f -> forall A0, term_multi_bracket_left (f /\1 (unitt A0))
| term_multi_bracket_left_at_right : forall A, forall A0 B0 (f : arrows A0 B0), term_multi_bracket_left f -> term_multi_bracket_left ((unitt A) /\1 f).

Hint Constructors term_multi_bracket_left.

(**OLD NOT USED
Fixpoint head_from_term_multi_bracket_left (A B : objects) (f : arrows A B) (Hterm : term_multi_bracket_left f) {struct Hterm} : nodes_arrows f.

Proof.
destruct Hterm.
- exact ( self_arrows (multi_bracket_left A B C Dlist)).
- exact (at_left_up (head_from_term_multi_bracket_left A B f Hterm) (unitt A0)).
- exact (at_right_up (unitt A) (head_from_term_multi_bracket_left A0 B0 f Hterm)).
Defined.
**)

(*
nodal_bracket_left <: nodal_arrow

nodal_arrow

nodal_arrow {A : object} {x : A} {Y : object} (f : arrow (object_at_node x) Y)
: { B : objects & { f' : arrow A B & object_at_node (f' x) = Y : Prop (* f' restr x = f : Prop *) } }

def term_arrow
term_bracket_left <: term_arrow
term_multi_bracket_left <: term_arrow

def nodal_arrow {A : object} {x : A} {Y : object} (f : arrow (object_at_node x) Y)
: { B : objects & { f' : arrow A B & term_arrow f' * head_from_term_arrow f' = (_, _, f) : Prop * object_at_node (f' x) = Y : Prop } }
nodal_bracket_left <: nodal_arrow
nodal_multi_bracket_left <: nodal_arrow


*)
(*
Fixpoint restr (A B : objects) (f : arrows A B) (x : A) : arrows ( object_at_node x ) (object_at_node (f x))
*)

Inductive term_arrow {A' B'} (f' : arrows A' B') : forall A B, arrows A B -> Set :=
| term_arrow_self : term_arrow f' f'
| term_arrow_at_left : forall A B (f : arrows A B), term_arrow f' f -> forall A0, term_arrow f' (f /\1 (unitt A0))
| term_arrow_at_right : forall A, forall A0 B0 (f : arrows A0 B0), term_arrow f' f -> term_arrow f' ((unitt A) /\1 f).

Hint Constructors term_arrow.


Definition cat_term_arrow_on_nodes_target :
  forall A' B' (f' : arrows A' B') A B (f : arrows A B),
    term_arrow f' f -> B' -> B.

  intros ? ? ? ? ? ? term_arrow_f'_f.
  induction term_arrow_f'_f as [ | A B f term_arrow_f'_f IH_term_arrow_f'_f A0 | A A0 B0 f term_arrow_f'_f IH_term_arrow_f'_f ].
  - exact (fun y => y).
  - exact (fun y => at_left (IH_term_arrow_f'_f y) A0).
  - exact (fun y => at_right A (IH_term_arrow_f'_f y)).
Defined.

Coercion cat_term_arrow_on_nodes_target : term_arrow >-> Funclass.

(*
Lemma lem004330 : forall A M (f : arrows A M)
                         (x : A) Y (f' : arrows (object_at_node x) Y) 
                         (term_arrow_f'_f : term_arrow f' f),
                    ( (f x) = cat_term_arrow_on_nodes_target term_arrow_f'_f (f' (self (object_at_node x))) ).
*)

Definition nodal_arrow {A : objects} {x : A} {Y : objects} (f : arrows (object_at_node x) Y)
: { M : objects & { f' : arrows A M & { term_arrow_f_f' : (term_arrow f f') &
                                ( (f' x) = term_arrow_f_f' (f (self (object_at_node x))) ) } } }.

  induction x as [ A | A x IHx B | A B x IHx ].
  - split with Y.
    split with f.
    split with (term_arrow_self f).
    auto.
  - destruct (IHx f) as (IHx_M & IHx_f' & IHx_prop).
    split with (IHx_M /\ B).
    split with (IHx_f' /\1 unitt B).
    destruct IHx_prop as (IHx_term_arrow & IHx_cat_term_arrow).
    split with (term_arrow_at_left IHx_term_arrow _) .
    replace ((IHx_f' /\1 unitt B) (at_left x B)) with (at_left (IHx_f' x) B) by auto.
    rewrite IHx_cat_term_arrow;  reflexivity.
  - destruct (IHx f) as (IHx_M & IHx_f' & IHx_prop).
    split with (A /\ IHx_M).
    split with ((unitt A) /\1 IHx_f').
    destruct IHx_prop as (IHx_term_arrow & IHx_cat_term_arrow).
    split with (term_arrow_at_right _ IHx_term_arrow) .
    replace ((unitt A /\1 IHx_f') (at_right A x)) with (at_right A (IHx_f' x)) by auto.
    rewrite IHx_cat_term_arrow;  reflexivity.
Defined.

(*
Definition nodal_arrow {A : objects} {x : A} {Y : objects} (f : arrows (object_at_node x) Y)
: { M : objects & { f' : arrows A M & prod (term_arrow f f') 
                                ( object_at_node (f' x) = object_at_node (f (self (object_at_node x))) ) } }.

  induction x as [ A | A x IHx B | A B x IHx ].
  - split with Y.
    split with f.
    auto.
  - destruct (IHx f) as (IHx_M & IHx_f' & IHx_prop).
    split with (IHx_M /\ B).
    split with (IHx_f' /\1 unitt B).
    destruct IHx_prop; auto.
  - destruct (IHx f) as (IHx_M & IHx_f' & IHx_prop).
    split with (A /\ IHx_M).
    split with ((unitt A) /\1 IHx_f').
    destruct IHx_prop; auto.
Defined.

Definition nodal_arrow {A : objects} {x : A} {Y : objects} (f : arrows (object_at_node x) Y)
: { M : objects & { f' : arrows A M & term_arrow f f' } }.

  induction x as [ A | A x IHx B | A B x IHx ].
  - split with Y.
    split with f.
    auto.
  - destruct (IHx f) as (IHx_M & IHx_f' & IHx_prop).
    split with (IHx_M /\ B).
    split with (IHx_f' /\1 unitt B).
    auto.
  - destruct (IHx f) as (IHx_M & IHx_f' & IHx_prop).
    split with (A /\ IHx_M).
    split with ((unitt A) /\1 IHx_f').
    auto.
Defined.
*)

Scheme Equality for letters.
Print letters_beq.
Print letters_eq_dec.
Scheme Equality for objects.
Print objects_beq.
Print objects_eq_dec.

(*Scheme Equality for nodes.*)
Fixpoint nodes_beq {A : objects} (x y : A) {struct x}: bool.

Proof.
  destruct x as [A | A x B | A B x].
  - destruct y.
    + exact true.
    + exact false.
    + exact false.
  - dependent destruction y.
    + exact false.
    + exact (nodes_beq A x y).
      Guarded.
    + exact false.
  - dependent destruction y.
    + exact false.
    + exact false.
    + exact (nodes_beq B x y).
Defined.
  
Lemma nodes_eq_dec {A : objects} (x y : A)  : {x = y} + {x <> y}.

Proof.
  remember (nodes_beq x y) as beq eqn: H_beq_x_y.
  destruct beq.
  + left.
    induction x as [A | A x IHx B | A B x IHx]; dependent destruction y; idtac "stopp";
    solve [ reflexivity
          | discriminate H_beq_x_y
          | replace (nodes_beq (at_left x B) (at_left y B)) with (nodes_beq x y) in H_beq_x_y by auto;
            cut (x = y); [
              intros ->; reflexivity
            | eauto ]
          | replace (nodes_beq (at_right A x) (at_right A y)) with (nodes_beq x y) in H_beq_x_y by auto;
            cut (x = y) ; [
              intros ->; auto
            | eauto ] ].
  + right.
    induction x as [A | A x IHx B | A B x IHx]; dependent destruction y;
    solve [ discriminate
          | discriminate H_beq_x_y
          | replace (nodes_beq (at_left x B) (at_left y B)) with (nodes_beq x y) in H_beq_x_y by auto;
            cut (x <> y); [
              intros J; contradict J; dependent destruction J; reflexivity
            | eauto]
          | replace (nodes_beq (at_right A x) (at_right A y)) with (nodes_beq x y) in H_beq_x_y by auto;
            cut (x = y) ; [
              intros J; contradict J; dependent destruction J; reflexivity
            | eauto] ].
Defined.
Hint Resolve nodes_eq_dec.



Definition nodal_multi_bracket_left {A : objects} {x : A} {A2 B2 C2 Dlist2} (H_object_at_node: object_at_node x = up_0 A2 ((B2 /\ C2) /\\ Dlist2))
: { M : objects & { f' : arrows A M & { term_arrow_f_f' : (term_arrow (multi_bracket_left A2 B2 C2 Dlist2) f') & prod ( (f' x) = term_arrow_f_f' ((multi_bracket_left A2 B2 C2 Dlist2) (self (A2 /\ ((B2 /\ C2) /\\ Dlist2)))) ) (forall n l : nodes A, ( n = x -> Empty_set) -> n <r l -> f' n <r f' l) } } }.

  induction x as [ A | A x IHx B | A B x IHx ].
  - simpl in H_object_at_node; subst A.
    split with (((A2 /\ B2) /\ C2) /\\ Dlist2);
    split with (multi_bracket_left A2 B2 C2 Dlist2).
    split with (term_arrow_self (multi_bracket_left A2 B2 C2 Dlist2)).
    split.
    + auto.
    + auto.
  - destruct (IHx H_object_at_node) as (IHx_M & IHx_f' & IHx_prop).
    split with (IHx_M /\ B);
    split with (IHx_f' /\1 unitt B).
    destruct IHx_prop as (IHx_term_arrow & IHx_cat_term_arrow & IHx_nonvariance).
    split with (term_arrow_at_left IHx_term_arrow _).
    split.
    + replace ((IHx_f' /\1 unitt B) (at_left x B)) with (at_left (IHx_f' x) B) by auto.
      rewrite IHx_cat_term_arrow;  reflexivity.
    + intros n l H_n_is_not_focusnode H_ltr.
      dependent destruction H_ltr.
      * constructor.
      * (* n is at_left x0 B , l is at_left y B *)
        { destruct (nodes_eq_dec x0 x) as [Heq_x0_x | Hneq_x0_x].
          - subst x0.
            elimtype Empty_set; auto.
          - cut (x0 = x -> Empty_set) ;[ | intros; exfalso; auto ].
            constructor; eauto.
        }
      * constructor; assumption.
  - destruct (IHx H_object_at_node) as (IHx_M & IHx_f' & IHx_prop).
    split with (A /\ IHx_M);
    split with (unitt A /\1 IHx_f').
    destruct IHx_prop as (IHx_term_arrow & IHx_cat_term_arrow & IHx_nonvariance).
    split with (term_arrow_at_right _ IHx_term_arrow).
    split.
    + replace ((unitt A /\1 IHx_f') (at_right A x)) with (at_right A (IHx_f' x)) by auto.
      rewrite IHx_cat_term_arrow;  reflexivity.
    + intros n l H_n_is_not_focusnode H_ltr.
      dependent destruction H_ltr.
      * constructor.
      * constructor; assumption.
      * (* n is at_left x0 B , l is at_left y B *)
        { destruct (nodes_eq_dec x0 x) as [Heq_x0_x | Hneq_x0_x].
          - subst x0.
            elimtype Empty_set; auto.
          - cut (x0 = x -> Empty_set) ;[ | intros; exfalso; auto ].
            constructor; eauto.
        }
Defined.


(** HERE **)

(**OLD NOT USED
Inductive node_is_self_or_at_left : forall A : objects, nodes A -> Prop :=
| node_is_self_or_at_left_cons1 : forall A, node_is_self_or_at_left (self A)
| node_is_self_or_at_left_cons2 : forall B C, node_is_self_or_at_left (at_left (self B) C)
| node_is_self_or_at_left_cons3 : forall B (y : nodes B) C D, node_is_self_or_at_left (at_left y C) -> node_is_self_or_at_left (at_left (at_left y C) D)
| node_is_self_or_at_left_cons4 : forall B (y : nodes B) C D, node_is_self_or_at_left (at_right C y) -> node_is_self_or_at_left (at_left (at_right C y) D)
| node_is_self_or_at_left_cons5 : forall B (y : nodes B) C D, node_is_self_or_at_left (at_left y C) -> node_is_self_or_at_left (at_right D (at_left y C))
| node_is_self_or_at_left_cons6 : forall B (y : nodes B) C D, node_is_self_or_at_left (at_right C y) -> node_is_self_or_at_left (at_right D (at_right C y)).
Hint Constructors node_is_self_or_at_left.

Goal forall (A B C D E: objects) (x: nodes A), node_is_self_or_at_left (at_right B (at_left (self A) C)).
auto. Abort.

Goal forall (A B C D E: objects) (x: nodes A), node_is_self_or_at_left (at_left (at_left (self A) C) B).
auto. Abort.

Goal forall (A B C D E: objects) (x: nodes A), node_is_self_or_at_left (at_right B (self A)).
Fail progress auto. Abort.

Goal forall (A B C D E: objects) (x: nodes A), node_is_self_or_at_left (at_right B (at_right C (self A))).
Fail progress auto. Abort.
**)

Inductive node_is_self : forall A : objects, nodes A -> Set :=
| node_is_self_cons1 : forall A, node_is_self (self A).
Hint Constructors node_is_self.

Inductive node_is_left_self : forall A : objects, nodes A -> Set :=
| node_is_left_self_cons1 : forall B C, node_is_left_self (at_left (self B) C)
| node_is_left_self_cons2 : forall B (y : nodes B) C D, node_is_left_self (at_left y C) -> node_is_left_self (at_left (at_left y C) D)
| node_is_left_self_cons3 : forall B (y : nodes B) C D, node_is_left_self (at_right C y) -> node_is_left_self (at_left (at_right C y) D)
| node_is_left_self_cons4 : forall B (y : nodes B) C D, node_is_left_self (at_left y C) -> node_is_left_self (at_right D (at_left y C))
| node_is_left_self_cons5 : forall B (y : nodes B) C D, node_is_left_self (at_right C y) -> node_is_left_self (at_right D (at_right C y)).
Hint Constructors node_is_left_self.

Inductive node_is_right_self : forall A : objects, nodes A -> Set :=
| node_is_right_self_cons1 : forall B C, node_is_right_self (at_right C (self B))
| node_is_right_self_cons2 : forall B (y : nodes B) C D, node_is_right_self (at_left y C) -> node_is_right_self (at_left (at_left y C) D)
| node_is_right_self_cons3 : forall B (y : nodes B) C D, node_is_right_self (at_right C y) -> node_is_right_self (at_left (at_right C y) D)
| node_is_right_self_cons4 : forall B (y : nodes B) C D, node_is_right_self (at_left y C) -> node_is_right_self (at_right D (at_left y C))
| node_is_right_self_cons5 : forall B (y : nodes B) C D, node_is_right_self (at_right C y) -> node_is_right_self (at_right D (at_right C y)).
Hint Constructors node_is_right_self.

Fixpoint node_start (A : objects) (x : A) {struct x} : node_is_self x + (node_is_left_self x + node_is_right_self x).

destruct x as [A | A0 x' A1 | A0 A1 x'].
- left.
  constructor.
- destruct x' as [A0 | A00 x'' A01 | A00 A01 x''] eqn:Heq; [
    right; left; constructor
  | destruct (node_start _ x') as [IH_node_start | [IH_node_start | IH_node_start]]; [
      subst x'; dependent destruction IH_node_start
    | right; left; constructor; subst x'; assumption
    | right; right; constructor; subst x'; assumption ] .. ].
- destruct x' as [A1 | A10 x'' A11 | A10 A11 x''] eqn:Heq; [
    right; right; constructor
  | destruct (node_start _ x') as [IH_node_start | [IH_node_start | IH_node_start]]; [
      subst x'; dependent destruction IH_node_start
    | right; left; constructor; subst x'; assumption
    | right; right; constructor; subst x'; assumption ] .. ].
Defined.

(**COMPLEX
Fixpoint node_start (A : objects) (x : A) {struct x} : nat.

destruct x as [A | A0 x' A1 | A0 A1 x'].
- exact O.
- destruct x' as [A0 | A00 x'' A01 | A00 A01 x''] eqn:Heq.
  + exact 1.
  + exact (node_start _ x').
  + exact (node_start _ x').
- destruct x' as [A1 | A10 x'' A11 | A10 A11 x''] eqn:Heq.
  + exact 2.
  + exact (node_start _ x').
  + exact (node_start _ x').
Defined.
Print node_start.
*)

(**NOPROGRESS
Function  node_start (A : objects) (x : A) {struct x} : nat :=
  match x with
  | self _ => 0
  | at_left A0 x' _ =>
      match x' as n0  with
      | self A2 => 1
      | at_left A00 x'' A01 =>
          node_start x'
      | at_right A00 A01 x'' =>
          node_start x'
      end
  | at_right _ A1 x' =>
      match x' with
      | self A2 =>  2
      | at_left A10 x'' A11 =>
          node_start x'
      | at_right A10 A11 x'' =>
          node_start x'
      end
  end.
(* Warning: Cannot build inversion information *)
**)


(**FAIL
Fixpoint node_start (A : objects) (x : A) {struct x} : nat.

destruct x as [A | A0 x' A1 | A0 A1 x'].
- exact O.
- destruct x' as [A0 | A00 x'' A01 | A00 A01 x''].
  + exact 1.
  + exact (node_start _ (at_left x'' A01)).
  + exact (node_start _ (at_right A00 x'')).
- destruct x' as [A1 | A10 x'' A11 | A10 A11 x''].
  + exact 2.
  + exact (node_start _ (at_left x'' A11)).
  + exact (node_start _ (at_right A10 x'')).
Defined. FAIL**)

Fixpoint lengthl (A : objects) : nat.
destruct A as [l | A1 A2].
- exact 1.
- exact ((lengthl A1) + (lengthl A2)).
Defined.

Lemma lem005100 (A : objects) : 1 <= lengthl A. 
induction A; simpl; auto with zarith.
Defined.
Hint Resolve lem005100.

(**OLD NOT USED
Fixpoint lengthn (A : objects) (node_x : A) : nat.
Proof.
destruct node_x as [A | A node_x B | A B node_x].
- exact 1.
- exact ((lengthn A node_x) + (lengthl B)).
- exact ((lengthl A) + (lengthn B node_x)).
Defined.
**)

Lemma lem005200 (l : letters) (x : letter l) : x = self (letter l).

dependent destruction x;
reflexivity.
Defined.
Hint Resolve lem005200.

Lemma lem005300 (A B : objects) (f : arrows_assoc A B) (x : A)
: forall (l : letters) (H_object_at_node : object_at_node x = letter l),
    object_at_node (f x) = letter l.

  induction f.
  - auto.
  - dependent destruction x.
    + intros; dependent destruction H_object_at_node.
    + auto.
    + dependent destruction x.
      * intros; dependent destruction H_object_at_node.
      * auto.
      * auto.
  - dependent destruction x.
    + intros; dependent destruction H_object_at_node.
    + dependent destruction x.
      * intros; dependent destruction H_object_at_node.
      * auto.
      * auto.
    + auto.
  - dependent destruction x. 
    + intros; dependent destruction H_object_at_node.
    + eapply IHf1.
    + eapply IHf2.
  - simpl; intros; eapply IHf2; eapply IHf1; assumption.
Defined.
Hint Resolve lem005300.
Hint Rewrite lem005300 using eauto.
Print Rewrite HintDb core.

(**OLD NOT USED
Lemma lem005400 (A : objects) (node_x : A): 1 <= lengthn node_x. 
induction node_x; simpl in *; auto with zarith.
Defined.
Hint Resolve lem005400.
**)

Lemma lem005500 (A : objects) (x y : A) (Heq : x = y) : x <e y.
rewrite Heq; auto.
Defined.
Hint Resolve lem005500.

Lemma lem005600 (A : objects) (x y : A) (H_rel : (y <l x) + (y <e x) + (y <r x) + (x <l y)) : (x <r y -> False).

  revert H_rel.
  intros   [ [ [ H_rel | H_rel ] | H_rel ] | H_rel ];
    intros H_ltr; dependent induction H_rel; dependent destruction H_ltr; auto.
Defined.
Hint Resolve lem005600.



Lemma lem005800 (A : objects) (x : A) : lengthl (object_at_node x) <=  lengthl A.
  induction x; simpl in *; auto with zarith.
Defined.
Hint Resolve lem005800.

Lemma lem005900 (A : objects) (x : A) (H_lengthl_at_node : lengthl A = lengthl (object_at_node x))
: x = self A.
  induction x as [A | A' x IHx A0 | A0 A' x IHx]; [
    reflexivity
  | exfalso;
    simpl in H_lengthl_at_node;
    cut (lengthl (object_at_node x) <=  lengthl A') ; [
      cut (1 <= lengthl A0) ; [
        auto with zarith
      | auto ]
    | auto ] .. ].
Defined.
Hint Resolve lem005900.

Lemma lem006000 (A B : objects) (f : arrows_assoc A B) : lengthl A = lengthl B.
  induction f; simpl in *; auto with zarith.
Defined.
Hint Resolve lem006000.


(**OLD NOT USED
Fixpoint multi_bracket_left_source (A : objects) : objects.

Proof.
destruct A as [l | A1 A2].
- exact (letter l).
- exact (A1 /\ multi_bracket_left_source A2).
Defined.

Fixpoint multi_bracket_right_source (A : objects) : objects.

Proof.
destruct A as [l | A1 A2].
- exact (letter l).
- exact (multi_bracket_right_source A1 /\ A2).
Defined.
**)


Inductive lt_left_once : forall A : objects, A -> A -> Set :=
| lt_left_once_cons1 : forall B C, lt_left_once (self (B /\ C)) (at_left (self B) C)
| lt_left_once_cons2 : forall B C (x y : nodes B), lt_left_once x y -> lt_left_once (at_left x C) (at_left y C)
| lt_left_once_cons3 : forall B C (x y : nodes B), lt_left_once x y -> lt_left_once (at_right C x) (at_right C y).
Hint Constructors lt_left_once.

Inductive lt_right_once : forall A : objects, A -> A -> Set :=
| lt_right_once_cons1 : forall B C, lt_right_once (self (C /\ B)) (at_right C (self B))
| lt_right_once_cons2 : forall B C (x y : nodes B), lt_right_once x y -> lt_right_once (at_left x C) (at_left y C)
| lt_right_once_cons3 : forall B C (x y : nodes B), lt_right_once x y -> lt_right_once (at_right C x) (at_right C y).
Hint Constructors lt_right_once.

Inductive lt_left : forall A : objects, A -> A -> Set :=
| lt_left_cons1 : forall B (z : nodes B) C, lt_left (self (B /\ C)) (at_left z C)
| lt_left_cons2 : forall B C (x y : nodes B), lt_left x y -> lt_left (at_left x C) (at_left y C)
| lt_left_cons3 : forall B C (x y : nodes B), lt_left x y -> lt_left (at_right C x) (at_right C y).
Hint Constructors lt_left.

Inductive lt_right : forall A : objects, A -> A -> Set :=
| lt_right_cons1 : forall B (z : nodes B) C, lt_right (self (C /\ B)) (at_right C z)
| lt_right_cons2 : forall B C (x y : nodes B), lt_right x y -> lt_right (at_left x C) (at_left y C)
| lt_right_cons3 : forall B C (x y : nodes B), lt_right x y -> lt_right (at_right C x) (at_right C y).
Hint Constructors lt_right.

Inductive lt_par : forall A : objects, A -> A -> Set :=
| lt_par_cons1 : forall B (x : nodes B) C (y : nodes C), lt_par (at_left x C) (at_right B y)
| lt_par_cons2 : forall B C (x y : nodes B), lt_par x y -> lt_par (at_left x C) (at_left y C)
| lt_par_cons3 : forall B C (x y : nodes B), lt_par x y -> lt_par (at_right C x) (at_right C y).
Hint Constructors lt_par.

(** lt_same is iso to eq restricted to [nodes A] datatype
Inductive lt_same : forall A : objects, A -> A -> Set :=
| lt_par_cons1 : forall B (x : nodes B), lt_same x x
| lt_par_cons2 : forall B C (x y : nodes B), lt_par x y -> lt_par (at_left x C) (at_left y C)
| lt_par_cons3 : forall B C (x y : nodes B), lt_par x y -> lt_par (at_right C x) (at_right C y).
*)

Inductive lt_same : forall A : objects, A -> A -> Set :=
| lt_same_cons1 : forall A, lt_same (self A) (self A)
| lt_same_cons2 : forall B C (x y : nodes B), lt_same x y -> lt_same (at_left x C) (at_left y C)
| lt_same_cons3 : forall B C (x y : nodes B), lt_same x y -> lt_same (at_right C x) (at_right C y).
Hint Constructors lt_same.

Fixpoint node_is_left_self_less (A : objects) (node_x : A) (H_node_is_left_self : node_is_left_self node_x) : nodes A.
destruct H_node_is_left_self.
- exact (self (B /\ C)).
- exact (at_left (node_is_left_self_less _ _ H_node_is_left_self) D).
- exact (at_left (node_is_left_self_less _ _ H_node_is_left_self) D).
- exact (at_right D (node_is_left_self_less _ _ H_node_is_left_self)).
- exact (at_right D (node_is_left_self_less _ _ H_node_is_left_self)).
Defined.

Fixpoint node_is_right_self_less (A : objects) (node_x : A) (H_node_is_right_self : node_is_right_self node_x) : nodes A.
destruct H_node_is_right_self.
- exact (self (C /\ B)).
- exact (at_left (node_is_right_self_less _ _ H_node_is_right_self) D).
- exact (at_left (node_is_right_self_less _ _ H_node_is_right_self) D).
- exact (at_right D (node_is_right_self_less _ _ H_node_is_right_self)).
- exact (at_right D (node_is_right_self_less _ _ H_node_is_right_self)).
Defined.

Lemma lem006100 (A : objects) (x y : A) (H_lt_left_once : lt_left_once x y) : lt_left x y.
  induction H_lt_left_once; simpl in *; auto.
Defined.
Hint Resolve lem006100.

Lemma lem006200 (A : objects) (x y : A) (H_lt_right_once : lt_right_once x y) : lt_right x y.
  induction H_lt_right_once; simpl in *; auto.
Defined.
Hint Resolve lem006200.

Lemma lem006300 (A : objects) (x : A) : forall y, (lt_same x y + lt_same y x) + ((lt_left x y + (lt_right x y + lt_par x y)) + (lt_left y x + (lt_right y x + lt_par y x))).

induction x.
- destruct y; auto.
- intros y; dependent destruction y; solve [ auto 7 
  | specialize IHx with y; decompose sum IHx; auto 7 ].
- intros y; dependent destruction y; solve [ auto 7 
  | specialize IHx with y; decompose sum IHx; auto 7 ].
Defined.
Hint Resolve lem006300.

Lemma lem006400 (A : objects) (x : nodes A) : forall y, lt_same x y -> eq x y.
  induction x; [
    destruct y; intros H_lt_same;
    solve [ auto 
          | dependent destruction H_lt_same; auto]
  |  dependent destruction y; intros H_lt_same; 
     try solve [ auto 
               | dependent destruction H_lt_same
               | dependent destruction H_lt_same;
                 try reflexivity;
                 apply IHx in H_lt_same;
                 f_equal; assumption] .. ].
Defined. 
Hint Resolve lem006400.

Lemma lem006500 (A : objects) (x : nodes A) : forall y, eq x y -> lt_same x y.
destruct 1. induction x; auto.
Defined.
Hint Resolve lem006500.


Lemma lem006600 (A : objects) (x : nodes A) : forall y, (lt_same x y) -> (eq y x).
intros y ?; cut (eq x y); auto.
Defined.
Hint Resolve lem006600.

Lemma lem006700 (A : objects) (x : nodes A) : forall y, (eq y x) -> (lt_same x y).
intros y ?; cut (eq x y); auto.
Defined.
Hint Resolve lem006700.

Lemma lem006800 (A : objects) (x : A) : forall y, (eq x y) + ((lt_left x y + (lt_right x y + lt_par x y)) + (lt_left y x + (lt_right y x + lt_par y x))).

intros y.
assert (H_iso : (lt_same x y + lt_same y x) + ((lt_left x y + (lt_right x y + lt_par x y)) + (lt_left y x + (lt_right y x + lt_par y x)))) by auto.
decompose sum H_iso; auto.
Defined.
Hint Resolve lem006800.

Notation lt_leftorright x y := (sum (lt_left x y) (lt_right x y)).
Notation lt_leftorright_or x y := (sum (lt_leftorright x y) (lt_leftorright y x)).
Notation lt_par_or x y := (sum (lt_par x y) (lt_par y x)).

Notation lt_left_eq x y := (sum (eq x y) (lt_left x y)).
Notation lt_right_eq x y := (sum (eq x y) (lt_right x y)).
Notation lt_leftorright_eq x y := (sum (eq x y) (lt_leftorright x y)).
Notation lt_leftorright_or_eq x y := (sum (eq x y) (lt_leftorright_or x y)).

Notation lt_no_medium x y := (forall w : nodes _, lt_leftorright x w -> lt_leftorright w y -> Empty_set).

Lemma lem006900 (A : objects) (x : A) : forall y, (eq x y) + (lt_par_or x y + lt_leftorright_or x y).
intros y.
assert (H_iso : (lt_same x y + lt_same y x) + ((lt_left x y + (lt_right x y + lt_par x y)) + (lt_left y x + (lt_right y x + lt_par y x)))) by auto.
decompose sum H_iso; auto.
Defined.
Hint Resolve lem006900.

Lemma lem007000 (A : objects) (x y : A)
 (H_eq : eq x y)
 (H_lt_par_or : lt_par_or x y)
: Empty_set.

  destruct H_eq;
  induction x;
  destruct H_lt_par_or as [H_lt_par_or | H_lt_par_or];
  dependent destruction H_lt_par_or;
  eauto.
Defined.
Hint Resolve lem007000.

Lemma lem007100 (A : objects) (x y : A)
 (H_eq : eq x y)
 (H_lt_leftorright_or : lt_leftorright_or x y)
: Empty_set.

  (** same tac as [eq] , [lt_par_or] **)
  destruct H_eq;
  induction x;
  destruct H_lt_leftorright_or as [[H_lt_leftorright_or | H_lt_leftorright_or] | [H_lt_leftorright_or | H_lt_leftorright_or]];
  dependent destruction H_lt_leftorright_or;
  eauto.
Defined.
Hint Resolve lem007100.

Lemma lem007200 (A : objects) (x : A) : forall (y : A)
 (H_lt_par_or : lt_par_or x y)
 (H_lt_leftorright_or_eq : lt_leftorright_or_eq x y),
 Empty_set.

  Time induction x;
  intros y [H_lt_par_or | H_lt_par_or] [H_lt_leftorright_or | [[H_lt_leftorright_or | H_lt_leftorright_or] | [H_lt_leftorright_or | H_lt_leftorright_or]]];
  dependent destruction H_lt_par_or;
  dependent destruction H_lt_leftorright_or;
  eapply IHx; eauto (** eauto alone [Time] at 68 seconds, but preceding with eapply [Time] at 2 seconds **).
Defined.
Hint Resolve lem007200.

Lemma lem007300 (A : objects) (x : A) : forall (y : A)
 (H_lt_leftorright : lt_leftorright x y)
 (H_lt_leftorright_rev : lt_leftorright y x),
 Empty_set.

  Time induction x;
  intros y [H_lt_leftorright | H_lt_leftorright] [H_lt_leftorright_rev | H_lt_leftorright_rev];
  dependent destruction H_lt_leftorright;
  dependent destruction H_lt_leftorright_rev;
  eapply IHx; eauto (** eauto alone [Time] at 33 seconds, but preceding with eapply [Time] at 1 seconds **).
Defined.
Hint Resolve lem007300.

(** this lem007300_post is particular with same proof of upcoming lem008800_pre'' below **)
Lemma lem007300_post (A : objects) (x : nodes A) : forall (y : nodes A)
 (H_lt_before_1 : lt_par x y)
 (H_lt_before_2 : lt_par y x),
 Empty_set.

  Time induction x;
  intros y H_lt_before_1 H_lt_before_2;
  dependent destruction H_lt_before_1;
  dependent destruction H_lt_before_2;
  eapply IHx; eauto (** eauto alone [Time] at 116 seconds, but preceding with eapply [Time] at 2 seconds **).
Defined.
Hint Resolve lem007300_post.

Lemma lem007400 (A : objects) (x : A) : forall (y : A)
 (H_lt_left : lt_left x y)
 (H_lt_right : lt_right x y),
 Empty_set.

  Time induction x;
  intros;
  dependent destruction H_lt_left;
  dependent destruction H_lt_right;
  eapply IHx; eauto (** eauto alone [Time] at 8 seconds, but preceding with eapply [Time] at 0 seconds **).
Defined.
Hint Resolve lem007400.


Lemma lem007500 (A : objects) (x y : nodes A)
 (H_lt_left : lt_left x y)
 (H_no_medium : lt_no_medium x y)
 : lt_left_once x y.

  induction H_lt_left; [
    destruct z; [
      constructor
    | elimtype Empty_set;
      specialize H_no_medium with (at_left (self _) _);      
      auto .. ]
  | constructor;
    apply IHH_lt_left; (**/!\ named automatically *)
    intros w H_lt_leftorright_1 H_lt_leftorright_2;
    specialize H_no_medium with (at_left w _) 
                                  || specialize H_no_medium with (at_right _ w) ;
    apply H_no_medium;
    decompose sum H_lt_leftorright_1;
    decompose sum H_lt_leftorright_2;
    auto .. ].
Defined.
Hint Resolve lem007500.

(** lemmas for disjoint cases come before this .. **)
(** this lem007500_rev to be renamed to lem007600 **)
Lemma lem007500_rev (A : objects) (x y : nodes A)
 (H_lt_left_once : lt_left_once x y)
 : lt_no_medium x y.

  induction H_lt_left_once; [
    intros w [H_lt_leftorright_1 | H_lt_leftorright_1] [H_lt_leftorright_2 | H_lt_leftorright_2];
    (dependent destruction H_lt_leftorright_1;
     do 2 (dependent destruction H_lt_leftorright_2))
  | (*Time*) intros w [H_lt_leftorright_1 | H_lt_leftorright_1] [H_lt_leftorright_2 | H_lt_leftorright_2];
    dependent destruction w;
    solve [
        do 2 dependent destruction H_lt_leftorright_1
      | do 2 dependent destruction H_lt_leftorright_2
      | dependent destruction H_lt_leftorright_1;
        dependent destruction H_lt_leftorright_2;
        eapply IHH_lt_left_once;
        eauto (** (+) eauto still needed after to prove some subgoals containing [existensials which were created by eapply] , (+) eauto alone is slower and is 13 seconds, but with eapply total is 1 seconds **)
      ]
          .. ].
Defined.
Hint Resolve lem007500_rev.
Notation lem_lt_left_once_medium := lem007500_rev.

Lemma lem007500_rev' (A : objects) (x y : nodes A)
      (H_lt_left_once : lt_left_once x y)
: {w : nodes A & prod (lt_leftorright x w) (lt_leftorright w y)} -> Empty_set.

  intros (H_medium_1 & H_medium_2 & H_medium_3);
  eapply lem_lt_left_once_medium;
  eassumption.
Defined.
Hint Resolve lem007500_rev'.

Lemma lem007500_rev'' (A : objects) (x y : nodes A)
      (H_medium : {w : nodes A & prod (lt_leftorright x w) (lt_leftorright w y)})
: lt_left_once x y -> Empty_set.

  eauto.
Defined.
Hint Resolve lem007500_rev''.

(**define tensor_nodes letter_nodes 
or alternatively define none bracket_left noce bracket_right wich breaks the node*)

Inductive object_is_letter : objects -> Set :=
object_is_letter_cons : forall l, object_is_letter (letter l).
Hint Constructors object_is_letter.

Inductive object_is_tensor : objects -> Set :=
object_is_tensor_cons : forall A B, object_is_tensor (A /\ B).
Hint Constructors object_is_tensor.


Notation node_is_letter x := (object_is_letter (object_at_node x)). 
Notation node_is_tensor x := (object_is_tensor (object_at_node x)).
(*Notation node_is_letter A x := (object_is_letter (object_at_node (x : nodes A))). 
Notation node_is_tensor A x := (object_is_tensor (object_at_node (x : nodes A))). 
*)

Lemma lem008100 (A : objects) : object_is_letter A + object_is_tensor A.
destruct A; auto.
Defined.
Hint Resolve lem008100.

Lemma lem008200 (A : objects) (x : nodes A) : node_is_letter x + node_is_tensor x.
destruct x; auto.
Defined.
Hint Resolve lem008200.

Lemma lem008300 (A : objects) (x : nodes A)
 (H_node_is_letter : node_is_letter x)
 (H_node_is_tensor : node_is_tensor x)
 : Empty_set.

  dependent destruction H_node_is_letter (** x1 eq **);
  dependent destruction H_node_is_tensor (** x eq **);
  rewrite <- x1 in x;
  dependent destruction x.
Defined.
Hint Resolve lem008300.

Lemma lem008400 (A : objects) (x : nodes A)
 (H_node_is_tensor : node_is_tensor x)
 (H_node_is_letter : node_is_letter x)
 : Empty_set.
eauto.
Defined. (** necessary? useful? .. **)
Hint Resolve lem008400.

Lemma lem008300' (A : objects)
 (H_object_is_letter : object_is_letter A)
 (H_object_is_tensor : object_is_tensor A)
 : Empty_set.

  dependent destruction H_object_is_letter;
  dependent destruction H_object_is_tensor.
Defined.
Hint Resolve lem008300'.


(**MEMO: SAME PROOF HOLD FOR ALT CONCLUSION BELOW /!\
Lemma lem008500 (A : objects) (w : nodes A) (H_node_is_letter : node_is_letter w)
 (y : nodes A) (H_lt_leftorright : lt_leftorright w y)
 : node_is_letter y.

  dependent destruction H_node_is_letter (** x eq **);
  destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright]; [
  induction H_lt_leftorright ; [
    dependent destruction x
  | dependent destruction H_lt_leftorright; auto .. ] .. ].
Defined.
Hint Resolve lem008500.
**)

(**REVIEW: exfalso?**)
Lemma lem008500 (A : objects) (w : nodes A) (H_node_is_letter : node_is_letter w)
 (y : nodes A) (H_lt_leftorright_eq : lt_leftorright_eq w y)
 : w = y.

  dependent destruction H_node_is_letter (** x eq **);
  destruct H_lt_leftorright_eq as [H_lt_leftorright_eq | [H_lt_leftorright_eq | H_lt_leftorright_eq]]; [
    assumption
  | induction H_lt_leftorright_eq ; [
      dependent destruction x
    | dependent destruction H_lt_leftorright_eq; auto .. ] .. ].
Defined.
Hint Resolve lem008500.
Hint Rewrite <- lem008500 using eauto.

Lemma lem008600 (A : objects) (w : nodes A) (H_node_is_letter : node_is_letter w)
 (y : nodes A) (H_lt_leftorright_eq : lt_leftorright_eq w y)
 : node_is_letter y.

autorewrite * with core using assumption. 
(*(**alt*) replace y with w by auto; assumption.*)
Defined.
Hint Resolve lem008600.


Notation node_is_lettery f w := 
  (prod
     ( forall (x : nodes _), lt_leftorright_eq w x -> lt_leftorright_eq (f w) (f x) )
     ( forall (x : nodes _), lt_leftorright_eq (f w) (f x) -> lt_leftorright_eq ((rev f) (f w)) ((rev f) (f x)) )).

(**OLD
Notation node_is_lettery f w := (node_is_tensor (w : nodes _)%type -> (forall x : nodes _,
 lt_leftorright w x -> lt_leftorright (f w) (f x) ) ) (**NOTE: scope stack trick*). *)
(**FINER? (lt_right x w -> lt_right (f x) (f w)) ) ) .. *)
(**FULLER?
prod (prod (lt_left x w -> lt_left (f x) (f w)) (lt_left (f x) (f w) -> lt_left x w))
(prod (lt_right x w -> lt_right (f x) (f w)) (lt_right (f x) (f w) -> lt_right x w)))).*)
(**FULLER? prod (lt_left w x -> lt_left (f w) (f x)) (lt_left (f w) (f x) -> lt_left w x) 
prod (lt_right w x -> lt_right (f w) (f x)) (lt_right (f w) (f x) -> lt_right w x) *)

(**NO
Lemma lem008300 (A B : arrows) (f : arrows_assoc A B)
 (x : nodes A) (H_lettery_node : node_is_lettery f x)
: ?? (H_object_at_node : object_at_node node_x = object_at_node (f node_x))
**)

(**>>> HERE <<<<**)

Lemma lem008700_pre (A B : objects) (f : arrows_assoc A B)
 (x : nodes A) (H_node_is_letter : node_is_letter x)
: node_is_letter (f x).
  
  dependent destruction H_node_is_letter;
  autorewrite * with core using constructor.
Defined.
Hint Resolve lem008700_pre.

Lemma lem008700 (B : objects)
 (w : nodes B) (H_node_is_letter : node_is_letter w)
 (A : objects) (f : arrows_assoc B A)
: node_is_lettery f w.

  split; intros x; intros;
  [ replace x with w by auto; auto
  | cut (node_is_letter (f w)); 
    [ replace (f x) with (f w) by auto; auto
    | auto 
    ]
  ].
Defined.
Hint Resolve lem008700.


Notation lt_before x y := (sum (lt_par x y) (sum (lt_right x y) (lt_left y x))).
Notation lt_after x y := (sum (lt_par y x) (sum (lt_left x y) (lt_right y x))).

Lemma lem008800_pre (A : objects) (x y : nodes A) : 
  (lt_before x y -> lt_after y x).

intuition.
Defined.
Hint Resolve lem008800_pre.
Lemma lem008800_pre' (A : objects) (x y : nodes A) : 
  (lt_after y x -> lt_before x y).

intuition.
Defined.
Hint Resolve lem008800_pre'.

Lemma lem008800_pre'' (A : objects) (x : nodes A) : forall (y : nodes A)
 (H_lt_before_1 : lt_before x y)
 (H_lt_before_2 : lt_before y x),
 Empty_set.

  Time induction x;
  intros y [H_lt_before_1 | [H_lt_before_1 | H_lt_before_1]] [H_lt_before_2 | [H_lt_before_2 | H_lt_before_2]];
  dependent destruction H_lt_before_1;
  dependent destruction H_lt_before_2;
  eapply IHx; eauto (** eauto alone [Time] at 116 seconds, but preceding with eapply [Time] at 2 seconds **).
Defined.
Hint Resolve lem008800_pre''.

Lemma lem008800 (A B : objects) (f : arrows_assoc A B)
 (x y : nodes A) (H_lt_before : lt_before x y)
: lt_before (f x) (f y).

  induction f.
  - assumption.
  - Time (dependent destruction x; [ | | dependent destruction x (**/!\ name*)]);
    (dependent destruction y; [ | | dependent destruction y (**/!\ name*)]);
    destruct H_lt_before as [H_lt_before | [H_lt_before | H_lt_before]];
    dependent destruction H_lt_before;
    solve [ dependent destruction H_lt_before
          | left; constructor; auto; dependent destruction H_lt_before; auto
          | right; left; constructor; auto; dependent destruction H_lt_before; auto
          | right; right; constructor; auto; dependent destruction H_lt_before; auto].
  (**Time 16 seconds*)
  - Time (dependent destruction x; [ | dependent destruction x (**/!\ name*) | ]);
    (dependent destruction y; [ | dependent destruction y (**/!\ name*) | ]);
    destruct H_lt_before as [H_lt_before | [H_lt_before | H_lt_before]];
    dependent destruction H_lt_before;
    solve [ dependent destruction H_lt_before
          | left; constructor; auto; dependent destruction H_lt_before; auto
          | right; left; constructor; auto; dependent destruction H_lt_before; auto
          | right; right; constructor; auto; dependent destruction H_lt_before; auto].
    (**Time 14 seconds*)
  - Time dependent destruction x;
    dependent destruction y;
    destruct H_lt_before as [H_lt_before | [H_lt_before | H_lt_before]];
    dependent destruction H_lt_before;
    solve [ dependent destruction H_lt_before
          | left; constructor; auto
          | right; left; constructor; auto
          | right; right; constructor; auto
          | cut (lt_before (f1 x) (f1 y)) (**/!\ name x y*); [
              intros [ | [ | ] ];
              solve [
                  left; constructor; auto
                | right; left; constructor; auto
                | right; right; constructor; auto ]
            | apply IHf1 (**/!\ name IHf1*); auto ]
          | cut (lt_before (f2 x) (f2 y)) (**/!\ name x y*); [
              intros [ | [ | ] ];
              solve [
                  left; constructor; auto
                | right; left; constructor; auto
                | right; right; constructor; auto ]
            | apply IHf2 (**/!\ name IHf2*); auto ]
          ].
    (**Time 50 seconds *)
  - simpl; auto.
Defined.
Hint Resolve lem008800.

(**silly **)
Lemma lem008800' (A B : objects) (f : arrows_assoc A B)
 (x y : nodes A) (H_lt_before : lt_before y x)
: lt_before (f y) (f x).

auto.
Defined.
Hint Resolve lem008800'.

(**/!\ new lt_left is same as old lt_for_left, 
   /!\ SILLY IT IS THE SAME PRESENTATION **)
Lemma lem008900 (A : objects) (x y : nodes A)
      (H_lt_for_left : lt_for_left x y)
: lt_left x y. 

  induction H_lt_for_left;
  auto.
Defined.
Hint Resolve lem008900.

Lemma lem009000 (A : objects) (x y : nodes A)
      (H_lt_left : lt_left x y)
: lt_for_left x y. 

  induction H_lt_left;
  auto.
Defined.
Hint Resolve lem009000.

Lemma lem009100 (A : objects) (x y : nodes A)
      (H_lt_for_right : lt_for_right x y)
: lt_right x y. 

  induction H_lt_for_right;
  auto.
Defined.
Hint Resolve lem009100.

Lemma lem009200 (A : objects) (x y : nodes A)
      (H_lt_right : lt_right x y)
: lt_for_right x y. 

  induction H_lt_right;
  auto.
Defined.
Hint Resolve lem009200.

(**MEMORY: lem00110 above is
Lemma lem00110' (B : objects) : forall A (H_eq : B = (A /\ B)),
  Empty_set.

induction B; intros; simplify_eq H_eq; eauto.
Defined. **)


(** tac_transivitity_lt is copy paste of Local Ltac le_lt_trans above **)
Local Ltac tac_transitivity_lt := le_lt_trans.

Lemma lem00410' : forall A, forall (x y z : nodes A), lt_leftorright_eq x y -> lt_leftorright_eq y z -> lt_leftorright_eq x z.
  
  induction x;
  dependent destruction y;
  dependent destruction z;
  intros [Hxy | [Hxy | Hxy]] [Hyz | [Hyz | Hyz]];
  solve [ auto 7
        | dependent destruction Hxy
        | dependent destruction Hyz
        | dependent destruction Hxy;
          dependent destruction Hyz;
          (cut (lt_leftorright_eq x z) 
               || (cut (lt_leftorright_eq y z) 
                       || cut (lt_leftorright_eq z z))) ; [
            intros [ | [ | ] ] ; [
              left; f_equal; auto
            | right; left; constructor; auto
            | right; right; constructor; auto ]
          | eauto 7
          ]
        ].
Defined.
Hint Resolve lem00410'.

Lemma lem00610' : forall A, forall (x y z : nodes A), lt_right x y -> lt_right y z -> lt_right x z.

  tac_transitivity_lt x y z.
Defined.
Hint Resolve lem00610'.

Lemma lem00710' : forall A, forall (x y z : nodes A), lt_right x y -> lt_leftorright_eq y z -> lt_right x z.

  intros A x y z Hxy [Hyz | [Hyz | Hyz]];
  revert A x y z Hxy Hyz.
  - tac_transitivity_lt x y z. 
  - tac_transitivity_lt x y z.
  - tac_transitivity_lt x y z.
Defined.
Hint Resolve lem00610'.

Lemma lem01010' : forall A, forall (x y : nodes A), lt_right x y -> lt_right_eq x y.

  auto.
Defined.
Hint Resolve lem01010'.

(** this lem01110' is same as non-case of [eq x y] , [lt_right x y] above at lem007100**)
Lemma lem01110' : forall A, forall (x : nodes A), lt_right x x -> Empty_set.

  eauto.
Defined.
Hint Resolve lem01110'.

(** more general than preceding older lem01210 **)
Lemma lem01210'' : forall A, forall (x : nodes A), lt_right (x) (self A) -> Empty_set.

  intros A x Hlt;
  dependent destruction Hlt.
Defined.
Hint Resolve lem01210''.

(** similar done already at lem007300 and lem007100
Lemma lem01310 : forall A, forall x y : nodes A, y <r x -> x <e y -> Empty_set.
**)

Lemma lem00610'' : forall A, forall (x y z : nodes A), lt_left x y -> lt_left y z -> lt_left x z.

  tac_transitivity_lt x y z.
Defined.
Hint Resolve lem00610''.

Lemma lem00710'' : forall A, forall (x y z : nodes A), lt_left x y -> lt_leftorright_eq y z -> lt_left x z.

  intros A x y z Hxy [Hyz | [Hyz | Hyz]];
  revert A x y z Hxy Hyz.
  - tac_transitivity_lt x y z. 
  - tac_transitivity_lt x y z.
  - tac_transitivity_lt x y z.
Defined.
Hint Resolve lem00610''.


Lemma lem01010'' : forall A, forall (x y : nodes A), lt_left x y -> lt_left_eq x y.

  auto.
Defined.
Hint Resolve lem01010''.

Lemma lem01110'' : forall A, forall (x : nodes A), lt_left x x -> Empty_set.

  eauto.
Defined.
Hint Resolve lem01110''.

Lemma lem01210''' : forall A, forall (x : nodes A), lt_left (x) (self A) -> Empty_set.

  intros A x Hlt;
  dependent destruction Hlt.
Defined.
Hint Resolve lem01210'''.




(**>>>>HERE<<<<
 show left_once between node_is_left_self node_x and node_less node_x **)

(** lt_left_once x y * lt_right w y * lt_right w x is accepted **)
Lemma lem009300 (A : objects) (x y : nodes A)
 (H_lt_left_once : lt_left_once x y)
 : (forall w : nodes A, (lt_par y w + lt_left w y) -> lt_before w x -> Empty_set).

  induction H_lt_left_once; [
   intros w [H_lt_before_1 | H_lt_before_1] [H_lt_before_2 | [H_lt_before_2 | H_lt_before_2]];
    dependent destruction H_lt_before_1;
    dependent destruction H_lt_before_2;
    dependent destruction H_lt_before_1
    (* case lt_right y w  with lt_left x w is possible *)
  | (*Time*) intros w [H_lt_before_1 | H_lt_before_1] [H_lt_before_2 | [H_lt_before_2 | H_lt_before_2]];
    dependent destruction w;
    solve [
        do 2 dependent destruction H_lt_before_1
      | do 2 dependent destruction H_lt_before_2
      | dependent destruction H_lt_before_1;
        dependent destruction H_lt_before_2;
        eapply IHH_lt_left_once with w (**/!\ name w **);
        auto
      ] .. ].
Defined.
Hint Resolve lem009300.

(** lt_right_once x y * lt_left w y * lt_left w x is accepted **)
Lemma lem009300' (A : objects) (x y : nodes A)
 (H_lt_right_once : lt_right_once x y)
 : (forall w : nodes A, (lt_par w y + lt_right w y) -> lt_before x w -> Empty_set).

  induction H_lt_right_once; [
   intros w [H_lt_before_1 | H_lt_before_1] [H_lt_before_2 | [H_lt_before_2 | H_lt_before_2]];
    dependent destruction H_lt_before_1;
    dependent destruction H_lt_before_2;
    dependent destruction H_lt_before_1
    (* case lt_left y w  with lt_right x w is possible *)
  | (*Time*) intros w [H_lt_before_1 | H_lt_before_1] [H_lt_before_2 | [H_lt_before_2 | H_lt_before_2]];
    dependent destruction w;
    solve [
        do 2 dependent destruction H_lt_before_1
      | do 2 dependent destruction H_lt_before_2
      | dependent destruction H_lt_before_1;
        dependent destruction H_lt_before_2;
        eapply IHH_lt_right_once with w (**/!\ name w **);
        auto
      ] .. ].
Defined.
Hint Resolve lem009300'.


Notation lem_lt_left_once_medium' := lem009300.
Lemma lem009400 (A : objects) (x y : nodes A)
 (H_lt_left_once : lt_left_once x y)
 (H_medium : {w : nodes A & ((lt_par y w + lt_left w y) * lt_before w x)%type})
 : Empty_set.

decompose record H_medium;
eapply lem_lt_left_once_medium';
eauto.
Defined.
Hint Resolve lem009400.
(**?? lem009400_rev ??**)


Lemma lem009500 (A : objects) (node_x : A)
 (H_node_is_left_self : node_is_left_self node_x) 
: lt_left_once (node_is_left_self_less H_node_is_left_self) node_x.

induction H_node_is_left_self; simpl; auto.
Defined.
Hint Resolve lem009500.


Lemma lem009500' (A : objects) (node_x : A)
 (H_node_is_right_self : node_is_right_self node_x) 
: lt_right_once (node_is_right_self_less H_node_is_right_self) node_x.

induction H_node_is_right_self; simpl; auto.
Defined.
Hint Resolve lem009500'.



Lemma lem009600 (B A : objects) (f : arrows_assoc B A)
      (w : nodes B) (H_node_is_lettery : node_is_lettery f w)
      : node_is_lettery (rev f) (f w).

  destruct H_node_is_lettery as [H_node_is_lettery_f_w H_node_is_lettery_revf_fw].
  split.
  - intros fx; pose ((rev f) fx) as x;  replace fx with (f x) by (subst x; auto).
    auto (*apply  H_node_is_lettery_revf_fw *).
  - intros fx; replace ((rev f) (f w)) with w by auto;
    replace (rev (rev f)) with f by auto.
    auto (*apply H_node_is_lettery_f_w *).
Defined.
Hint Resolve lem009600.



(**>>>>>>>HERE<<<<<<<<<<*)
(**first prove left_once <-> no_medium , then prove by contradict **)

Lemma lem009700_pre (A : objects) (x y : nodes A)
 (H_lt_par : lt_par y x)
 : {w : nodes A & prod (lt_left w y) (lt_right w x)}.

induction H_lt_par.
- split with (self _); auto.
- destruct IHH_lt_par as (IHH_lt_par_w & ? & ?);
  split with (at_left IHH_lt_par_w _); auto.
- destruct IHH_lt_par as (IHH_lt_par_w & ? & ?);
  split with (at_right _ IHH_lt_par_w); auto.
Defined.
Hint Resolve lem009700_pre.

Lemma lem009700_pre' (A : objects) (x y : nodes A)
 (H_lt_par : lt_par y x)
: {w : nodes A & prod (lt_par y w + lt_left w y) (lt_before w x)}.

  cut ({w : nodes A & prod (lt_left w y) (lt_right w x)}) ; [
    intros (w & ? & ?); split with w; auto
  | auto ].
Defined.
Hint Resolve lem009700_pre'.

Lemma lem009700_pre'1 (A : objects) (x y : nodes A)
 (H_lt_par : lt_par x y)
: {w : nodes A & prod (lt_before x w) (lt_par w y + lt_right w y)}.

  cut ({w : nodes A & prod (lt_left w x) (lt_right w y)}) ; [
    intros (w & ? & ?); split with w; auto
  | auto ].
Defined.
Hint Resolve lem009700_pre'1.


Lemma lem009700_pre'' (A : objects) (x y : nodes A)
 (H_lt_left : lt_left x y)
 (H_no_medium : forall w : nodes A, (lt_par y w + (lt_left w y + lt_right w y)) -> lt_before w x -> Empty_set)
 : lt_left_once x y.


  induction H_lt_left.
 -   destruct z.
     + constructor.
    + elimtype Empty_set.
      specialize H_no_medium with (at_left (self _) _).
      eapply H_no_medium.
      * right; left; auto.
        * right. right. auto.
    + elimtype Empty_set.
      specialize H_no_medium with (at_left (self _) _).
      eapply H_no_medium.
      * right; auto.
        * right. right. auto.
          
 -  constructor.
    apply IHH_lt_left. (**/!\ named automatically *)
    intros w H_lt_leftorright_1 H_lt_leftorright_2.
    specialize H_no_medium with (at_left w C). 
    apply H_no_medium;
    decompose sum H_lt_leftorright_1;
    decompose sum H_lt_leftorright_2;
    eauto.

 -  constructor;
    apply IHH_lt_left; (**/!\ named automatically *)
    intros w H_lt_leftorright_1 H_lt_leftorright_2.

                                   specialize H_no_medium with (at_right C w) ;
    apply H_no_medium;
    decompose sum H_lt_leftorright_1;
    decompose sum H_lt_leftorright_2;
    eauto.

Defined.
Hint Resolve lem009700_pre''.


(**
Fail Lemma lem009700_pre''' (A : objects) (x y : nodes A)
 (H_lt_left_once : lt_left_once x y)
 : (forall w : nodes A, (lt_par y w + (lt_left w y + lt_right w y)) -> lt_before w x -> Empty_set). **)

Lemma lem007100' (A : objects) (x y : A)
 (H_eq : eq x y)
 (H_lt_leftorright : lt_leftorright x y)
: Empty_set.

eapply lem007100; eauto. 
Defined.
Hint Resolve lem007100'.

Lemma lem007100'' (A : objects) (x y : A)
 (H_eq : eq x y)
 (H_lt_leftorright : lt_leftorright y x)
: Empty_set.

eapply lem007100; eauto. 
Defined.
Hint Resolve lem007100''.

Lemma lem009700_pre'''' (A : objects) (x : A) : forall (y : A)

 (H_lt_leftorright_eq : lt_leftorright_eq x y)
 (H_lt_leftorright_rev : lt_leftorright y x),
 Empty_set.

intros; destruct H_lt_leftorright_eq as [H_lt_leftorright_eq | H_lt_leftorright_eq];
 [symmetry in H_lt_leftorright_eq; eapply lem007100 | eapply lem007300]; eauto.
Defined.
Hint Resolve lem009700_pre''''.

(*
Notation node_is_lettery_alt B y :=  (prod (forall (A : objects) (f : arrows_assoc B A) (x : nodes B),
  lt_leftorright_eq y x -> ((lt_par (f x) (f y))%type)%type + (lt_leftorright (f x) (f y))%type -> Empty_set)
 (forall (A : objects) (f : arrows_assoc B A) (x : nodes B),
  lt_leftorright_eq (f y) (f x) -> ((lt_par x y)%type)%type + (lt_leftorright x y)%type -> Empty_set)).
*)


Notation node_is_lettery_alt f w := 
  (prod
     ( forall (x : nodes _), lt_leftorright_eq w x -> lt_leftorright (f x) (f w) -> Empty_set )
     ( forall (x : nodes _), lt_leftorright_eq (f w) (f x) -> lt_leftorright ((rev f) (f x)) ((rev f) (f w)) -> Empty_set )).

(*
Notation node_is_lettery_alt B y :=  (prod (forall (A : objects) (f : arrows_assoc B A) (x : nodes B),
  lt_leftorright_eq y x -> (lt_leftorright (f x) (f y))%type -> Empty_set)
 (forall (A : objects) (f : arrows_assoc B A) (x : nodes B),
  lt_leftorright_eq (f y) (f x) -> (lt_leftorright x y)%type -> Empty_set)).
*)
Lemma lem009700_pre'''''  (B : objects) (w : nodes B)
      (A : objects) (f : arrows_assoc B A)
      (H_node_is_lettery : node_is_lettery f w) 
: node_is_lettery_alt f w.

  destruct H_node_is_lettery as [H_node_is_lettery_f_w  H_node_is_lettery_revf_fw];
  split.
  - intros x ?; cut (lt_leftorright_eq (f w) (f x)); [
      intros; eapply lem009700_pre''''; eauto 
    | auto (*apply H_node_is_lettery_f_w*) ].
  - intros x ?; cut (lt_leftorright_eq ((rev f) (f w)) ((rev f) (f x))) ; [
      intros; eapply lem009700_pre''''; eauto 
    | auto (*apply H_node_is_lettery_revf_fw*) ].
Defined.
Hint Resolve lem009700_pre'''''.

Lemma lem009700_pre6 (B : objects) (y : nodes B) (x : nodes B)
      (H_lt_left_once : lt_left_once x y)
      (A : objects) (f : arrows_assoc B A)
      (H_node_is_lettery : node_is_lettery f y)
: lt_left (f x) (f y).

  assert (H_lt_before : lt_before (f y) (f x)) by auto. Show Existentials.
  destruct H_lt_before as [H_lt_before | [H_lt_before | H_lt_before]];
    [ idtac
    | cut (lt_leftorright_eq y x); 
      [ intros; elimtype Empty_set; eapply lem009700_pre''''; eauto
      | replace y with ((rev f) (f y)) by auto; replace x with ((rev f) (f x)) by auto;
        destruct H_node_is_lettery as [H_node_is_lettery_1 H_node_is_lettery_2];
        apply H_node_is_lettery_2; auto (* = intuition*)
      ]
    | assumption 
    ].

  assert (fw : {fw : nodes A & prod (lt_par (f y) fw + lt_left fw (f y)) (lt_before fw (f x))}) by 
      auto (*apply lem009700_pre'; assumption*).
  destruct fw as (fw & H_fw_1 & H_fw_2).
  set ((rev f) fw) as w.
  replace fw with (f w) in * by (subst w; simpl; auto).
  assert (H_fw_1' : lt_before (f y) (f w) ) by (destruct H_fw_1; auto (* = intuition *)).
  assert (H_fw_1'' : lt_before ((rev f) (f y)) ((rev f) (f w)) ) by auto.
  replace ((rev f) (f y)) with y in  * by auto.
  replace ((rev f) (f w)) with w in  * by auto.
  assert (H_fw_2' : lt_before ((rev f) (f w)) ((rev f) (f x)) ) by auto.
  replace ((rev f) (f x)) with x in  * by auto.
  replace ((rev f) (f w)) with w in  * by auto.
  assert (H_fw_1''' : ((lt_par y w + lt_left w y) + lt_right y w)) by (decompose sum H_fw_1''; auto).
  destruct H_fw_1'''; [
      elimtype Empty_set; eapply lem009300 with (w:=w) (y:=y); eauto
    | assert (H_lt_leftorright_eq : lt_leftorright_eq (f y) (f w)) by (eapply H_node_is_lettery; auto);
      elimtype Empty_set;
      destruct H_fw_1 as [H_fw_1 | H_fw_1]; [
        destruct H_lt_leftorright_eq as [ | ]; eapply lem007200; eauto
      | eapply lem009700_pre''''; [eassumption| auto] ]].
  Show Existentials.
Defined.
Hint Resolve lem009700_pre6.


Lemma lem009700_pre6' (B : objects) (y : nodes B) (x : nodes B)
      (H_lt_left_once : lt_right_once x y)
      (A : objects) (f : arrows_assoc B A)
      (H_node_is_lettery : node_is_lettery f y)
: lt_right (f x) (f y).

  assert (H_lt_before : lt_before (f x) (f y)) by auto. Show Existentials.
  destruct H_lt_before as [H_lt_before | [H_lt_before | H_lt_before]];
    [ idtac
    | assumption (**all other cases are exfalso**)
    | cut (lt_leftorright_eq y x); 
      [ intros; elimtype Empty_set; eapply lem009700_pre''''; eauto
      | replace y with ((rev f) (f y)) by auto; replace x with ((rev f) (f x)) by auto;
        destruct H_node_is_lettery as [H_node_is_lettery_1 H_node_is_lettery_2];
        apply H_node_is_lettery_2; auto (* = intuition *)
      ]
    ].

  assert (fw : {fw : nodes A & prod (lt_before (f x) fw) (lt_par fw (f y) + lt_right fw (f y))}) by 
      auto (*apply lem009700_pre'; assumption*).
  destruct fw as (fw & H_fw_2 & H_fw_1).
  set ((rev f) fw) as w.
  replace fw with (f w) in * by (subst w; simpl; auto).
  assert (H_fw_1' : lt_before (f w) (f y) ) by (destruct H_fw_1; auto (* = intuition *)).
  assert (H_fw_1'' : lt_before ((rev f) (f w)) ((rev f) (f y)) ) by auto.
  replace ((rev f) (f y)) with y in  * by auto.
  replace ((rev f) (f w)) with w in  * by auto.
  assert (H_fw_2' : lt_before ((rev f) (f x)) ((rev f) (f w)) ) by auto.
  replace ((rev f) (f x)) with x in  * by auto.
  replace ((rev f) (f w)) with w in  * by auto.
  assert (H_fw_1''' : ((lt_par w y + lt_right w y) + lt_left y w)) by (decompose sum H_fw_1''; auto).
  destruct H_fw_1''';
    [ elimtype Empty_set; eapply lem009300' with (w:=w) (y:=y); eauto
    | assert (H_lt_leftorright_eq : lt_leftorright_eq (f y) (f w)) by (eapply H_node_is_lettery; auto);
      elimtype Empty_set;
      destruct H_fw_1 as [H_fw_1 | H_fw_1];
      [ destruct H_lt_leftorright_eq as [ | ]; 
        eapply lem007200; eauto
      | eapply lem009700_pre''''; 
        [ eassumption | auto ] 
      ]
    ].
  Show Existentials.
Defined.
Hint Resolve lem009700_pre6'.

Lemma lem009700_pre7 (B : objects) (y : nodes B) (x : nodes B)
      (A : objects) (f : arrows_assoc B A)
      (H_node_is_lettery : node_is_lettery f y)
      (H_lt_left_once : lt_left_once (f x) (f y))
: lt_left x y.

  assert (H_node_is_lettery_revf_fy : node_is_lettery (rev f) (f y)) by auto (*apply lem009600*).
  cut ( lt_left ((rev f) (f x)) ((rev f) (f y)) ); [
      replace ((rev f) (f x)) with x by auto; replace ((rev f) (f y)) with y by auto; tauto
    | auto (*apply lem009700_pre6 with (f:=rev f); assumption*)].
Defined.
Hint Resolve lem009700_pre7.

Lemma lem009700_pre7' (B : objects) (y : nodes B) (x : nodes B)
      (A : objects) (f : arrows_assoc B A)
      (H_node_is_lettery : node_is_lettery f y)
      (H_lt_right_once : lt_right_once (f x) (f y))
: lt_right x y.

  assert (H_node_is_lettery_revf_fy : node_is_lettery (rev f) (f y)) by auto (*apply lem009600*).
  cut ( lt_right ((rev f) (f x)) ((rev f) (f y)) ); [
      replace ((rev f) (f x)) with x by auto; replace ((rev f) (f y)) with y by auto; tauto
    | auto (*apply lem009700_pre6 with (f:=rev f); assumption*)].
Defined.
Hint Resolve lem009700_pre7'.

(** the case lt_left x y * lt_right x w * lt_leftorright w y is automatically excepted **)
Lemma lem007500' (A : objects) (x y : nodes A)
 (H_lt_left : lt_left x y)
 (H_no_medium : forall w : nodes A, lt_left x w -> lt_leftorright w y -> Empty_set)
 : lt_left_once x y.

  cut (forall w : nodes A, lt_leftorright x w -> lt_leftorright w y -> Empty_set);
  [ auto 
  | intros w [H_lt_leftorright_1 | H_lt_leftorright_1] H_lt_leftorright_2; [
      revert w H_lt_leftorright_1 H_lt_leftorright_2; assumption 
    | cut (lt_right x y); [
        intros; eapply lem007400; eassumption
      | eapply lem00710'; eauto ]
  ] ].
Defined.

Lemma lem007500_rev''' (A : objects) (x y : nodes A)
 (H_lt_left_once : lt_left_once x y)
 : (forall w : nodes A, lt_left x w -> lt_leftorright w y -> Empty_set).

  intros; eapply lem007500_rev; (eassumption || eauto).
Defined.



Lemma lem009700_pre8 (A B : objects) (x y : nodes A)
:      lt_leftorright_eq x y ->
       (lt_leftorright_eq (at_left x B) (at_left y B)).

  intuition. (* = ALT:
  intros [H_lt_leftorright_eq | [H_lt_leftorright_eq | H_lt_leftorright_eq]];
  [ left; f_equal 
  | right; left; constructor 
  | right; right; constructor
  ];
  auto. *)
Defined.
Hint Resolve lem009700_pre8.

Lemma lem009700_pre9 (A B : objects) (x y : nodes A)
:      lt_leftorright_eq x y ->
            (lt_leftorright_eq (at_right B x) (at_right B y)).

  intuition. (* = ALT:
  intros [H_lt_leftorright_eq | [H_lt_leftorright_eq | H_lt_leftorright_eq]];
  [ left; f_equal 
  | right; left; constructor 
  | right; right; constructor
  ];
  auto. *)
Defined.
Hint Resolve lem009700_pre9.


Lemma lem009700_pre10 (A : objects)
      (w y : nodes A) (H_lt_leftorright : lt_leftorright w y)
      : {u : nodes A & prod (lt_leftorright_eq w u) (lt_left_once u y + lt_right_once u y)}.

  destruct (node_start y) as [H_node_start | [H_node_start | H_node_start]].
  - destruct H_node_start.
    destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright];
      dependent destruction H_lt_leftorright.
  - split with (node_is_left_self_less H_node_start).
    split.
    + { induction H_node_start as [ | B ? C D | C ? B D | B ? C D | C ? B D ].
        - destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * left; reflexivity.
            * dependent destruction H_lt_leftorright.
          + do 2 dependent destruction H_lt_leftorright.
        - destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq (at_left (self (up_0 B C)) D)
                                     (at_left (node_is_left_self_less H_node_start) D)) ; 
              [ cut (lt_leftorright_eq (self (up_0 (up_0 B C) D)) (at_left (self (up_0 B C)) D)); 
                eauto (*eapply lem00410'*)            
              | specialize IHH_node_start with (self _);
                cut (lt_leftorright_eq (self (up_0 B C)) (node_is_left_self_less H_node_start)); 
                eauto (*eapply IHH_node_start*)
              ].
            * simpl;
              cut (lt_leftorright_eq x (node_is_left_self_less H_node_start)); 
              eauto (*eapply IHH_node_start*).
          + dependent destruction H_lt_leftorright.
            simpl;
              cut (lt_leftorright_eq x (node_is_left_self_less H_node_start)); 
              eauto (*eapply IHH_node_start*).
        - (*same proof command as case above*)
          destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq (at_left (self (up_0 B C)) D)
                                     (at_left (node_is_left_self_less H_node_start) D)) ; 
              [ cut (lt_leftorright_eq (self (up_0 (up_0 B C) D)) (at_left (self (up_0 B C)) D)); 
                eauto (*eapply lem00410'*)            
              | specialize IHH_node_start with (self _);
                cut (lt_leftorright_eq (self (up_0 B C)) (node_is_left_self_less H_node_start)); 
                eauto (*eapply IHH_node_start*)
              ].
            * simpl;
              cut (lt_leftorright_eq x (node_is_left_self_less H_node_start)); 
              eauto (*eapply IHH_node_start*).
          + dependent destruction H_lt_leftorright.
            simpl;
              cut (lt_leftorright_eq x (node_is_left_self_less H_node_start)); 
              eauto (*eapply IHH_node_start*).
        - destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq x (node_is_left_self_less H_node_start));
              eauto (*eapply IHH_node_start*).
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq (at_right D (self (up_0 B C)))
                                     (at_right D (node_is_left_self_less H_node_start)));
              [ cut (lt_leftorright_eq (self (up_0 D (up_0 B C))) (at_right D (self (up_0 B C))));
                eauto (*eapply lem00410'*)
              | specialize IHH_node_start with (self _);
                cut (lt_leftorright_eq (self (up_0 B C)) (node_is_left_self_less H_node_start));
                eauto (*eapply IHH_node_start*)
              ].
            * simpl;
              cut (lt_leftorright_eq x (node_is_left_self_less H_node_start));
              eauto (*eapply IHH_node_start*).
        - (*same proof command as case above*)
          destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq x (node_is_left_self_less H_node_start));
              eauto (*eapply IHH_node_start*).
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq (at_right D (self (up_0 B C)))
                                     (at_right D (node_is_left_self_less H_node_start)));
              [ cut (lt_leftorright_eq (self (up_0 D (up_0 B C))) (at_right D (self (up_0 B C))));
                eauto (*eapply lem00410'*)
              | specialize IHH_node_start with (self _);
                cut (lt_leftorright_eq (self (up_0 B C)) (node_is_left_self_less H_node_start));
                eauto (*eapply IHH_node_start*)
              ].
            * simpl;
              cut (lt_leftorright_eq x (node_is_left_self_less H_node_start));
              eauto (*eapply IHH_node_start*).
      }
    +  left; auto.
  - split with (node_is_right_self_less H_node_start).
    split.
    + { induction H_node_start as [ | B ? C D | C ? B D | B ? C D | C ? B D ].
        - destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + do 2 dependent destruction H_lt_leftorright.
          + dependent destruction H_lt_leftorright.
            * left; reflexivity.
            * dependent destruction H_lt_leftorright.
        - destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq (at_left (self (up_0 B C)) D)
                                     (at_left (node_is_right_self_less H_node_start) D)) ; 
              [ cut (lt_leftorright_eq (self (up_0 (up_0 B C) D)) (at_left (self (up_0 B C)) D)); 
                eauto (*eapply lem00410'*)            
              | specialize IHH_node_start with (self _);
                cut (lt_leftorright_eq (self (up_0 B C)) (node_is_right_self_less H_node_start)); 
                eauto (*eapply IHH_node_start*)
              ].
            * simpl;
              cut (lt_leftorright_eq x (node_is_right_self_less H_node_start)); 
              eauto (*eapply IHH_node_start*).
          + dependent destruction H_lt_leftorright.
            simpl;
              cut (lt_leftorright_eq x (node_is_right_self_less H_node_start)); 
              eauto (*eapply IHH_node_start*).
        - (*same proof command as case above*)
          destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq (at_left (self (up_0 B C)) D)
                                     (at_left (node_is_right_self_less H_node_start) D)) ; 
              [ cut (lt_leftorright_eq (self (up_0 (up_0 B C) D)) (at_left (self (up_0 B C)) D)); 
                eauto (*eapply lem00410'*)            
              | specialize IHH_node_start with (self _);
                cut (lt_leftorright_eq (self (up_0 B C)) (node_is_right_self_less H_node_start)); 
                eauto (*eapply IHH_node_start*)
              ].
            * simpl;
              cut (lt_leftorright_eq x (node_is_right_self_less H_node_start)); 
              eauto (*eapply IHH_node_start*).
          + dependent destruction H_lt_leftorright.
            simpl;
              cut (lt_leftorright_eq x (node_is_right_self_less H_node_start)); 
              eauto (*eapply IHH_node_start*).
        - destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq x (node_is_right_self_less H_node_start));
              eauto (*eapply IHH_node_start*).
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq (at_right D (self (up_0 B C)))
                                     (at_right D (node_is_right_self_less H_node_start)));
              [ cut (lt_leftorright_eq (self (up_0 D (up_0 B C))) (at_right D (self (up_0 B C))));
                eauto (*eapply lem00410'*)
              | specialize IHH_node_start with (self _);
                cut (lt_leftorright_eq (self (up_0 B C)) (node_is_right_self_less H_node_start));
                eauto (*eapply IHH_node_start*)
              ].
            * simpl;
              cut (lt_leftorright_eq x (node_is_right_self_less H_node_start));
              eauto (*eapply IHH_node_start*).
        - (*same proof command as case above*)
          destruct H_lt_leftorright as [H_lt_leftorright | H_lt_leftorright].
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq x (node_is_right_self_less H_node_start));
              eauto (*eapply IHH_node_start*).
          + dependent destruction H_lt_leftorright.
            * simpl;
              cut (lt_leftorright_eq (at_right D (self (up_0 B C)))
                                     (at_right D (node_is_right_self_less H_node_start)));
              [ cut (lt_leftorright_eq (self (up_0 D (up_0 B C))) (at_right D (self (up_0 B C))));
                eauto (*eapply lem00410'*)
              | specialize IHH_node_start with (self _);
                cut (lt_leftorright_eq (self (up_0 B C)) (node_is_right_self_less H_node_start));
                eauto (*eapply IHH_node_start*)
              ].
            * simpl;
              cut (lt_leftorright_eq x (node_is_right_self_less H_node_start));
              eauto (*eapply IHH_node_start*).
      }
    +  right; auto.
Defined.
Hint Resolve lem009700_pre10.

Lemma lem009700_pre11 (A : objects)
      (x y : nodes A) (H_lt_right_once : lt_right_once x y)
: node_is_right_self y.
  induction H_lt_right_once; 
  [ simpl; auto
  | dependent destruction IHH_lt_right_once; auto ..
  ].
Defined.
Hint Resolve lem009700_pre11.

Lemma lem009700_pre12 (A : objects)
      (x y : nodes A) (H_lt_left_once : lt_left_once x y)
: node_is_left_self y.
  induction H_lt_left_once; 
  [ simpl; auto
  | dependent destruction IHH_lt_left_once; auto ..
  ].
Defined.
Hint Resolve lem009700_pre12.

Lemma lem009700_pre13 (A : objects) (x : nodes A)
      (H_node_is_left_self : node_is_left_self x)
      (H_node_is_right_self : node_is_right_self x)
: Empty_set.
  
  induction H_node_is_left_self;
  dependent destruction H_node_is_right_self;
  eauto.
Defined.
Hint Resolve lem009700_pre13.

Lemma lem009700_pre14 (A : objects) (x : A) : forall y, (eq x y) + ((lt_before x y) + (lt_before y x)).

intros y.
assert (H_iso: (eq x y) + ((lt_left x y + (lt_right x y + lt_par x y)) + (lt_left y x + (lt_right y x + lt_par y x)))) by auto.
decompose sum H_iso; auto.
Defined.
Hint Resolve lem009700_pre14.

Lemma lem009700_pre15 (B : objects) (x y : nodes B)
      (A : objects) (f : arrows_assoc B A)
      (H_lt_before : lt_before (f x) (f y))
: lt_before x y.

  replace x with ((rev f) (f x)) by auto;
  replace y with ((rev f) (f y)) by auto.
  eauto.
Defined.
Hint Resolve lem009700_pre15.

Lemma lem009700_pre16 (A : objects) (u x y : nodes A)
      (H_lt_leftorright_u_y : lt_leftorright u y)
      (H_lt_par_u_x : lt_par u x)      
: lt_par y x.
  induction H_lt_par_u_x;
  destruct H_lt_leftorright_u_y as [H_lt_leftorright_u_y | H_lt_leftorright_u_y];
  dependent destruction H_lt_leftorright_u_y;
  eauto (*auto for base step*).
Defined.
Hint Resolve lem009700_pre16.


Lemma lem009700 (B : objects) 
      (A : objects) (f : arrows_assoc B A) (H_cumul_B : forall x y : nodes B, lt_right x y -> lt_right (f x) (f y))
      (y : nodes B) (H_node_is_lettery : node_is_lettery f y)
      (x : nodes B) (H_lt_left_once_x_y : lt_left_once x y)
: lt_left_once (f x) (f y).

  assert (H_lt_left_fx_fy : lt_left (f x) (f y)) by auto.
  apply lem007500'; [assumption | ].
  assert (H_no_medium_B :=(lem007500_rev H_lt_left_once_x_y)).
  intros fw (*; set ((rev f) fw) as w; replace fw with (f w) by (subst w; auto) *).
  intros H_lt_left_fx_fw H_lt_leftorright_fw_fy.
  assert (fu : {fu : nodes A & prod (lt_leftorright_eq fw fu) (lt_left_once fu (f y) + lt_right_once fu (f y))})
    by auto (* apply lem009700_pre10 *).
  (*set (f y) as fy in *.*)
  destruct (node_start (f y)) as [H_node_start_fy | [H_node_start_fy | H_node_start_fy]].
  -  dependent destruction H_node_start_fy.
     replace (f y) with (self A) in * by auto.
     dependent destruction H_lt_left_fx_fy.
  - destruct fu as (fu & H_lt_leftorright_eq_fw_fu & [ H_lt_left_once_fu_fy | H_lt_right_once_fu_fy ]);
    [ idtac
    | assert (H_node_start_fy' : node_is_right_self (f y)) by eauto;
      eapply lem009700_pre13; eassumption
    ].
    assert (H_lt_left_fx_fu : lt_left (f x) fu) by (eapply lem00710'' with (y:=fw); eauto).
    clear dependent fw.
    set ((rev f) fu) as u; replace fu with (f u) in * by (subst u; auto).
    assert (H_lt_left_u_y : lt_left u y) by eauto (* eapply lem009700_pre7 *).
    
    eapply H_no_medium_B with (w:=u);
      [ idtac
      | auto
      ].

    assert (H_lt_before_u_x : lt_before u x) 
      by (cut (lt_before (f u) (f x)); eauto).
    assert (H_rel : (eq x u) + ((lt_before x u) + (lt_before u x))) by auto.
    destruct H_rel as [H_rel | [H_rel | H_rel]].
    + elimtype Empty_set. 
      decompose sum H_lt_before_u_x; solve [eapply lem007000; eauto | eapply lem007100; eauto].
    + elimtype Empty_set;
      eapply lem008800_pre''; eassumption (* indeterminism? *).
    + destruct H_rel as [H_rel | [H_rel | H_rel]].
      * elimtype Empty_set.
        assert (H_rel' : lt_par y x) by eauto (* eapply lem009700_pre16 *).
        eapply lem007200; eauto.
      * elimtype Empty_set.
        assert (H_rel' : lt_right (f u) (f x)) by (apply H_cumul_B; assumption). (**/!\ H_cumul_B USED HERE **)
        eapply lem007300; eauto.
      * auto.
  - destruct fu as (fu & H_lt_leftorright_eq_fw_fu & [ H_lt_left_once_fu_fy | H_lt_right_once_fu_fy ]);
    [ 
      assert (H_node_start_fy' : node_is_left_self (f y)) by eauto;
      eapply lem009700_pre13; eassumption
    | idtac
    ].
    assert (H_lt_left_fx_fu : lt_left (f x) fu) by (eapply lem00710'' with (y:=fw); eauto).
    clear dependent fw.
    set ((rev f) fu) as u; replace fu with (f u) in * by (subst u; auto).
    assert (H_lt_left_u_y : lt_right u y) by eauto (* eapply lem009700_pre7' *).
    
    eapply H_no_medium_B with (w:=u);
      [ idtac
      | auto
      ].

    assert (H_lt_before_u_x : lt_before u x) 
      by (cut (lt_before (f u) (f x)); eauto).
    assert (H_rel : (eq x u) + ((lt_before x u) + (lt_before u x))) by auto.
    destruct H_rel as [H_rel | [H_rel | H_rel]].
    + elimtype Empty_set. 
      decompose sum H_lt_before_u_x; solve [eapply lem007000; eauto | eapply lem007100; eauto].
    + elimtype Empty_set;
      eapply lem008800_pre''; eassumption (* indeterminism? *).
    + destruct H_rel as [H_rel | [H_rel | H_rel]].
      * elimtype Empty_set.
        assert (H_rel' : lt_par y x) by eauto (* eapply lem009700_pre16 *).
        eapply lem007200; eauto.
      * elimtype Empty_set.
        assert (H_rel' : lt_right (f u) (f x)) by (apply H_cumul_B; assumption). (**/!\ H_cumul_B USED HERE **)
        eapply lem007300; eauto.
      * auto.
Defined.    
Hint Resolve lem009700.


(*
 re-memorize that the H_cumul_B hypothesis in lem009700 was used once to only exfalso the case
 lt_right (f x) fw * lt_left fw (f y) ,
 this signifies that all the other cases are still exfalso without this H_cumul_B hypothesis,
 which infers that lem009800 shall already be inside [part of symmetric lem009700_pre6' or lem009700_pre6'] *)
Lemma lem009800 (B : objects) (x y : nodes B)
      (H_lt_right_once : lt_right_once x y)
      (A : objects) (f : arrows_assoc B A)
      (H_node_is_lettery : node_is_lettery f y)
: (forall fw : nodes A, lt_right fw (f y) -> lt_right (f x) fw -> Empty_set).

  intros fw; set ((rev f) fw) as w; replace fw with (f w) by (subst w; auto);
  intros H_lt_right_fw_fy H_lt_right_fx_fw;
  assert (H_lt_before_x_w : lt_before ((rev f) (f x)) ((rev f) (f w))) by auto;
  assert (H_lt_before_w_y : lt_before ((rev f) (f w)) ((rev f) (f y))) by auto.
  replace ((rev f) (f x)) with x in H_lt_before_x_w by auto.
  replace ((rev f) (f w)) with w in H_lt_before_x_w, H_lt_before_w_y by auto.
  replace ((rev f) (f y)) with y in H_lt_before_w_y by auto.

  eapply lem009300' with (w:=w); try eassumption. 
  (*goal  lt_par w y + lt_right w y *)
  destruct H_lt_before_w_y as [ | [ | H_lt_left_y_w]];
    [ auto 
    | auto 
    | idtac
    ].
  
  assert (H_node_is_lettery_alt : node_is_lettery_alt f y) by auto.
  elimtype Empty_set;
    destruct H_node_is_lettery_alt as [H_node_is_lettery_alt _];
    eapply H_node_is_lettery_alt with (x:=w); (*OLD: with (f:=f) (x:=w)*)
    auto.
Defined.
Hint Resolve lem009800.

(* A /\ B
    E is B
    fy' : nodes (B) 
    fy' is letter l 
    H_no_medium comes from intros; assert lt_right {self <r} (at_right fw _) (at_right fy' _){=:fy} by constructor; eapply bigH
    get Dlist with letter l /\\ Dlist = B   *)

(*
Lemma lem009900_pre (B1 B2 A : objects) (f : arrows_assoc (B1 /\ B2) A)
      (w : nodes B1) (H_node_is_lettery : node_is_lettery f? (at_left w B2))
: node_is_lettery f? w

*)

(*
Lemma lem009800 above holds with [cumul_letteries B y = true]
as long as 
[(H_node_is_lettery : forall x : nodes B, cumul_letteries x = true -> node_is_lettery f x)]
of lem005700 below is well propagated.
short: from (H_node_is_lettery : forall x : nodes B, cumul_letteries x = true -> node_is_lettery f x)
       to  cumul_letteries x = true 
       to node_is_lettery f x
       to (forall fw : nodes A, lt_right fw (f y) -> lt_right (f x) fw -> Empty_set).
       to (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set))
       to {Dlist : list objects & foldright (object_at_node fy') Dlist = E}.
*)

(*
>>>>>>>>>>>>>>COMMENT<<<<<<<<<<<<<<<<<
(*

(*_____________________*)
(*BLOCK BACKUP COPY FROM BELOW*)

Fixpoint foldrightn (A : objects) (z : nodes A) (list_B : list objects) : nodes (foldright A list_B).

destruct list_B as [ | B list_C].
- exact z.
- exact (at_left (foldrightn A z list_C) B).
Defined.

Definition foldrightn_self (A : objects) (list_B : list objects) : nodes (foldright A list_B) :=
@foldrightn A (self A) list_B.
Hint Unfold foldrightn_self.

Lemma lem212 (A : objects) (list_B : list objects) : (object_at_node (foldrightn_self A list_B)) = A.

induction list_B; simpl in *; auto.
Defined.
Hint Resolve lem212.


Check eq_rect. Check nodes. Check eq_sym.
(*this lemma means that we can use loc_rev instead of general foldrightn, but we still use particular foldrightn_self*)
Lemma lem332 (A : objects) (z : nodes A) (list_B : list objects) : foldrightn z list_B = loc_rev (foldrightn_self A list_B) (eq_rect A nodes z (object_at_node (foldrightn_self A list_B)) (eq_sym (lem212 A list_B))).
induction list_B; simpl in *; auto.
Defined.



(*____________________*)

Fixpoint list_map A B (f : A -> B) (l : list A) : list B.

destruct l.
- exact nil.
- exact (cons (f a) (list_map A B f l)).
Defined.

Lemma list_map_nil A B (f : A -> B)(l : list A) (H_not_nil : l = nil -> Empty_set ) : (list_map f l = nil -> Empty_set).
destruct l.
intros; apply H_not_nil; reflexivity.
simpl. intros J3; discriminate J3.
Defined.
Hint Resolve list_map_nil.

Fixpoint list_from_no_medium (E : objects) (fy' : nodes E)
      (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set)) {struct fy'}
: list (nodes E).

  destruct fy'.
  * exact (cons (self A) nil).
  * assert (H_no_medium_A :  (forall fw : A, lt_right fw fy' -> Empty_set)) by
         (intros fw Htemp; eapply H_no_medium with (fw:=(at_left fw _)); auto).
     exact (cons (at_right _ (self B)) (list_map (fun t : nodes A => at_left t B) (list_from_no_medium A fy' H_no_medium_A))).
  * elimtype Empty_set; eapply H_no_medium with (fw:=self _); auto.
Defined.
Arguments list_from_no_medium [E] fy' H_no_medium.

Lemma list_from_no_medium_prop1 (E : objects) (fy' : nodes E) (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set))
: list_from_no_medium fy' H_no_medium = nil -> Empty_set.
destruct fy'. 
-simpl; intros J1; discriminate J1.
- simpl; intros J2; discriminate J2.
- elimtype Empty_set; eapply H_no_medium with (fw:=self _); auto.
Defined.
Arguments list_from_no_medium_prop1 [E] fy' H_no_medium _.

Definition list_split A (l : list A) (H_not_nil : l = nil -> Empty_set)  : {a : A & {l' : list A & l = cons a l'}}.
Proof.
destruct l.
elimtype Empty_set; apply H_not_nil; reflexivity.
split with a; split with l. reflexivity.
Defined.
Arguments list_split [A] l H_not_nil.

Fixpoint foldright' (l : list objects) (H_not_nil : l = nil -> Empty_set) {struct l} : objects.

Proof.
destruct l.
- elimtype Empty_set; apply H_not_nil; reflexivity.
- destruct l eqn:Heq_l.
  + exact o.
  + apply foldright' with (l:=l).
    intros ->; discriminate Heq_l.
Defined.
Arguments foldright' l H_not_nil.

Lemma list_from_no_medium_prop2 (E : objects) (fy' : nodes E) (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set))
: @foldright' (list_map (@object_at_node E) (list_from_no_medium fy' H_no_medium)) (list_map_nil (@object_at_node E)  (list_from_no_medium_prop1 fy' H_no_medium)) = E.

induction fy'.
- simpl. reflexivity.
- simpl list_from_no_medium. simpl list_map. simpl list_from_no_medium_prop1.  rewrite IHfy'. unfold foldright'.  simpl.


Lemma list_from_no_medium_prop2 (E : objects) (fy' : nodes E) (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set))
: let ls := list_split (list_from_no_medium fy' H_no_medium) (list_from_no_medium_prop1 fy' H_no_medium) in
foldright (object_at_node (projT1(ls))) (list_map (@object_at_node E) (projT1(projT2(ls)))) = E.

induction fy'.
- simpl. reflexivity.
-  simpl in *.
(*
Fixpoint foldrightn (A : objects) (z : nodes A) (list_B : list objects) : nodes (foldright A list_B).

destruct list_B as [ | B list_C].
- exact z.
- exact (at_left (foldrightn A z list_C) B).
Defined.

Definition foldrightn_self (A : objects) (list_B : list objects) : nodes (foldright A list_B) :=
@foldrightn A (self A) list_B.
Hint Unfold foldrightn_self.

Lemma lem212 (A : objects) (list_B : list objects) : (object_at_node (foldrightn_self A list_B)) = A.

induction list_B; simpl in *; auto.
Defined.
Hint Resolve lem212.

Fixpoint list_from_no_medium (E : objects) (fy' : nodes E)
      (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set)) {struct fy'}
: list objects.

  destruct fy'.
  * exact nil.
  * assert (H_no_medium_A :  (forall fw : A, lt_right fw fy' -> Empty_set)) by
         (intros fw Htemp; eapply H_no_medium with (fw:=(at_left fw _)); auto).
     exact (cons B (list_from_no_medium A fy' H_no_medium_A)).
  * elimtype Empty_set; eapply H_no_medium with (fw:=self _); auto.
Defined.
Arguments list_from_no_medium [E] fy' H_no_medium.

Lemma lem122 (E : objects) (fy' : nodes E)
      (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set))
      : (foldright (object_at_node fy') (list_from_no_medium fy' H_no_medium) = E).

induction fy'. 
- reflexivity. 
- simpl.  rewrite IHfy'. reflexivity.
- elimtype Empty_set; eapply H_no_medium with (fw:=self _); auto.
Defined.
Hint Resolve lem122.

Lemma lem123 (E : objects) (fy' : nodes E)
      (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set))
   : (foldrightn_self (object_at_node fy') (list_from_no_medium fy' H_no_medium)) = eq_rect E nodes fy' (foldright (object_at_node fy') (list_from_no_medium fy' H_no_medium)) (eq_sym (lem122 H_no_medium)). 

induction fy'.
reflexivity. simpl object_at_node. simpl list_from_no_medium. unfold foldrightn_self. simpl. unfold foldrightn_self in *. rewrite IHfy'.
unfold eq_rect in *. simpl in *.
simpl. rewrite IHfy'.
Check eq_rec.
Print Implicit eq_rec.

*)
>>>>>>>>>>>>>COMMENT<<<<<<<<<<<<<
*)*)

Fixpoint foldrightn (A : objects) (z : nodes A) (list_B : list objects) : nodes (foldright A list_B).

destruct list_B as [ | B list_C].
- exact z.
- exact (at_left (foldrightn A z list_C) B).
Defined.

Fixpoint foldrightn_self (A : objects) (list_B : list objects) {struct list_B} : nodes (foldright A list_B).

destruct list_B as [ | B list_C].
- exact (self A).
- exact (at_left (foldrightn_self A list_C) B).
Defined.

Lemma lem229 (A : objects) (z : nodes A) (list_B : list objects) : foldrightn (self A) list_B = foldrightn_self A list_B.

induction list_B; simpl; auto.
Defined.
Hint Resolve lem229.

Check eq_rect_r. Check eq_rect.

(**/!\ this constructive equality [objects_same] is used instead of the eq convertibility equality to solve
   coherence lacking from the transport [@eq_rect objects (A : objects) (nodes : objects -> Set) (x : nodes A) (B : objects) (Heq : A = B) : nodes B] on object-subterm : ... does [at_left] then [transport] convertible with [transport] then [at_left] ? which is: is transport coherent ? **)
Inductive objects_same : objects -> objects -> Set :=
| objects_same_cons1 : forall l, objects_same (letter l) (letter l)
| objects_same_cons2 : forall A A', objects_same A A' -> forall B B', objects_same B B' -> objects_same (A /\ B) (A' /\ B').
Hint Constructors objects_same.

Fixpoint objects_same_refl (A : objects) : objects_same A A.
destruct A.
- constructor.
- constructor.
  + apply (objects_same_refl A1).
  + apply (objects_same_refl A2).
Defined.
Hint Resolve objects_same_refl.

Definition objects_same_eq (A B : objects) (H_eq : A = B) : objects_same A B.
  
  rewrite <- H_eq; apply objects_same_refl.  Show Proof.
Defined.
Hint Unfold objects_same_eq.
Hint Resolve objects_same_eq.

Lemma lem133 (A : objects) : objects_same_eq eq_refl = objects_same_refl A.

  reflexivity.
Defined.  
Hint Resolve lem133.
Hint Rewrite lem133 using eauto.

Lemma objects_eq_same (A B : objects) (H_same : objects_same A B ) : A = B.

  induction H_same; subst; auto.
Defined.
Hint Resolve objects_eq_same.
Hint Rewrite objects_eq_same using eauto.

Fixpoint nodes_map (A B : objects) (H_objects_same : objects_same A B) {struct H_objects_same} : nodes A -> nodes B.

destruct H_objects_same.
- exact (fun x => x).
- intros x. dependent destruction x. 
  + exact (self _).
  + exact (at_left (nodes_map A A' H_objects_same1 x) B').
  + exact (at_right A' (nodes_map B B' H_objects_same2 x)).
Defined.
Print Implicit nodes_map.
Arguments nodes_map [A B] !H_objects_same !_.
Arguments multi_bracket_left /.

(**OLD NOT USED, SEE lem091 INSTEAD
Lemma lem098 (A1 A2 B1 B2 : objects) (H_objects_same1 : objects_same A1 B1) (H_objects_same2 : objects_same A2 B2)
: nodes_map (objects_same_cons2 H_objects_same1 H_objects_same2) (self _) = self _. 

reflexivity.
Defined.
Hint Resolve lem098.
Hint Rewrite lem098 using eauto.
**)

Lemma lem091 (B B' : objects) (H_objects_same2 : objects_same B B'): nodes_map H_objects_same2 (self B) = self B'.
destruct H_objects_same2; reflexivity.
Defined. Hint Resolve lem091. Hint Rewrite lem091 using eauto.

Lemma lem099 (A1 A2 B1 B2 : objects) (H_objects_same1 : objects_same A1 B1) (H_objects_same2 : objects_same A2 B2)
 (x : nodes A1)
: nodes_map (objects_same_cons2 H_objects_same1 H_objects_same2) (at_left x A2) = at_left (nodes_map H_objects_same1 x) B2.

reflexivity.
Defined.
Hint Resolve lem099.
Hint Rewrite lem099 using eauto.

Lemma lem100 (A1 A2 B1 B2 : objects) (H_objects_same1 : objects_same A1 B1) (H_objects_same2 : objects_same A2 B2)
 (x : nodes A2)
: nodes_map (objects_same_cons2 H_objects_same1 H_objects_same2) (at_right A1 x) = at_right B1 (nodes_map H_objects_same2 x).

reflexivity.
Defined.
Hint Resolve lem100.
Hint Rewrite lem100 using eauto.

Lemma lem212 (A : objects) (x : nodes A) :  nodes_map (objects_same_refl A) x = x.

  induction A.
  - reflexivity.
  - simpl objects_same_refl.
    dependent destruction x.
    + reflexivity.
    + simpl nodes_map. unfold solution_left; unfold block; unfold eq_rect_r; unfold eq_rect; simpl.
      f_equal. apply IHA1.
    + simpl nodes_map. unfold solution_left; unfold block; unfold eq_rect_r; unfold eq_rect; simpl.
      f_equal. apply IHA2.
Defined.
Hint Resolve lem212.
Hint Rewrite lem212 using eauto.

Lemma lem090 (A B : objects) (H_objects_same : objects_same A B)
 (x y : nodes A) (H_lt_right_once : lt_right_once x y)
: lt_right_once (nodes_map H_objects_same x) (nodes_map H_objects_same y).

induction H_objects_same.
- simpl; assumption.
- dependent destruction x; dependent destruction y; dependent destruction H_lt_right_once;
rewrite ?lem099; rewrite ?lem100; rewrite ?lem091; eauto.

(**OLD ALT:
induction H_objects_same; eauto.
dependent destruction x; dependent destruction y; dependent destruction H_lt_right_once.

simpl nodes_map; unfold solution_left; unfold eq_rect_r; unfold eq_rect. simpl. 
simpl nodes_map; unfold solution_left; unfold eq_rect_r; unfold eq_rect. simpl. 

Show. autorewrite * with core using eauto.
compute; constructor; apply IHH_objects_same1; assumption.
compute; constructor; apply IHH_objects_same2; assumption. **)
Defined.
Hint Resolve lem090.

Lemma lem090' (A B : objects) (H_objects_same : objects_same A B)
 (x y : nodes A) (H_lt_left_once : lt_left_once x y)
: lt_left_once (nodes_map H_objects_same x) (nodes_map H_objects_same y).

induction H_objects_same.
- simpl; assumption.
- dependent destruction x; dependent destruction y; dependent destruction H_lt_left_once;
rewrite ?lem099; rewrite ?lem100; rewrite ?lem091; eauto.

(**OLD ALT :
induction H_objects_same; eauto.
dependent destruction x; dependent destruction y; dependent destruction H_lt_left_once.


simpl nodes_map; unfold solution_left; unfold eq_rect_r; unfold eq_rect. simpl. 
simpl nodes_map; unfold solution_left; unfold eq_rect_r; unfold eq_rect. simpl. 
(*Lemma lem091 (B B' : objects) (H_objects_same2 : objects_same B B'): nodes_map H_objects_same2 (self B) = self B'.
induction H_objects_same2; auto.
Defined.
Hint Rewrite lem091 using eauto.*)
Show. autorewrite * with core using eauto.
compute; constructor; apply IHH_objects_same1; assumption.
compute; constructor; apply IHH_objects_same2; assumption. **)
Defined.
Hint Resolve lem090'.


Lemma lem009900 (E : objects) (fy' : nodes E)
(*      (H_node_is_letter : node_is_letter fy') (**does it extends to [node_is_lettery f y'] or to [cumul_letteries E fy' = true ->] ?*) (*solution: in fact the particular condition sougt was (lt_right fw fy' -> Empty_set) , 
 re-memorize that the H_cumul_B hypothesis in lem009700 was used once to only exfalso the case
 lt_right (f x) fw * lt_left fw (f y) ,
 this signifies that all the other cases are still exfalso without this H_cumul_B hypothesis,
 which infers that lem009800 shall already be inside [part of symmetric lem009700_pre6' or lem009700_pre6']*) *)
      (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set))
: {Dlist : list objects & 
   {H_same_foldright : objects_same (foldright (object_at_node fy') Dlist) E & 
    nodes_map H_same_foldright (foldrightn_self (object_at_node fy') Dlist) = fy' }}%type.

  induction fy' as [ A | A fy' IHfy' B | A B fy' IHfy'].
  * split with nil.
    split with (objects_same_refl A).
    simpl. auto.
  *  assert (H_no_medium_A :  (forall fw : A, lt_right fw fy' -> Empty_set)) by
         (intros fw Htemp; eapply H_no_medium with (fw:=(at_left fw _)); auto).
     specialize IHfy' with (1:=H_no_medium_A).
     destruct IHfy' as (IHfy'_Dlist & IHfy'_H_same_foldright & IHfy'_H_same_foldrightn_self).
     split with (cons B IHfy'_Dlist).
     simpl in *.
     split with (objects_same_cons2 (IHfy'_H_same_foldright) (objects_same_refl B)).
     simpl nodes_map. unfold solution_left; unfold block; unfold eq_rect_r; unfold eq_rect; simpl.
     f_equal. apply IHfy'_H_same_foldrightn_self.
     Guarded.
  * elimtype Empty_set; eapply H_no_medium with (fw:=self _); auto.
Defined.

(*
(* OLD*)
Lemma lem009900 (E : objects) (fy' : nodes E)
(*      (H_node_is_letter : node_is_letter fy') (**does it extends to [node_is_lettery f y'] or to [cumul_letteries E fy' = true ->] ?*) (*solution: in fact the particular condition sougt was (lt_right fw fy' -> Empty_set) , 
 re-memorize that the H_cumul_B hypothesis in lem009700 was used once to only exfalso the case
 lt_right (f x) fw * lt_left fw (f y) ,
 this signifies that all the other cases are still exfalso without this H_cumul_B hypothesis,
 which infers that lem009800 shall already be inside [part of symmetric lem009700_pre6' or lem009700_pre6']*) *)
      (H_no_medium : forall fw : nodes E, (lt_right fw fy' -> Empty_set))
: {Dlist : list objects & foldright (object_at_node fy') Dlist = E}.

  induction fy'.
  * (**/!\ OLD, NOT NECESSARY: dependent destruction H_node_is_letter.
    simpl in *; subst.*)
    split with nil; reflexivity.
  * (* simpl in H_node_is_letter.*)
     assert (J2 :  (forall fw : A, lt_right fw fy' -> Empty_set)) by
         (intros fw HJ2; eapply H_no_medium with (fw:=(at_left fw _)); auto).
     set (IHfy' (*H_node_is_letter*) J2) as J'.
     Guarded.
     destruct J' as (J'_Dlist & J'_eq).
     Guarded.
     split with (cons B J'_Dlist).
     simpl in J'_eq |- *.
     rewrite J'_eq; reflexivity.
     Guarded.
  * elimtype Empty_set; eapply H_no_medium with (fw:=self(A/\B)); auto.
Defined.
*)


Definition restr_left (B1 B2 : objects) (cumul_letteries : nodes (B1 /\ B2) -> bool) : nodes B1 -> bool
  := fun(z : B1) => cumul_letteries (at_left z B2).
Hint Unfold restr_left.
Hint Resolve restr_left.

Definition restr_right (B1 B2 : objects) (cumul_letteries : nodes (B1 /\ B2) -> bool) : nodes B2 -> bool
  :=  fun (z : B2) => cumul_letteries (at_right B1 z).
Hint Unfold restr_right.
Hint Resolve restr_right.

(*
Notation cumul_letteries_wellform' B cumul_letteries :=
  (prod (forall x : nodes B, node_is_letter x -> (cumul_letteries : nodes B -> bool) x = true) 
        (forall x y : nodes B, lt_leftorright x y -> cumul_letteries x = true -> cumul_letteries y = true)).
*)

Notation cumul_letteries_wellform' B cumul_letteries :=
  (forall x : nodes B, node_is_letter x -> cumul_letteries x = true).

Definition restr_left_wellform (B1 B2 : objects)
      (cumul_letteries : nodes (B1 /\ B2) -> bool)
      (H_cumul_letteries_wellform : cumul_letteries_wellform' (B1 /\ B2) cumul_letteries)
: forall (z : nodes B1), node_is_letter z -> (restr_left cumul_letteries) z = true :=

  fun (z : nodes B1) (H : node_is_letter z) => H_cumul_letteries_wellform (at_left z B2) H
(*
Proof.
intros; eapply H_cumul_letteries_wellform; assumption.
Show Proof.
*).
Hint Unfold restr_left_wellform.
Hint Resolve restr_left_wellform.

Definition restr_right_wellform (B1 B2 : objects)
      (cumul_letteries : nodes (B1 /\ B2) -> bool)
      (H_cumul_letteries_wellform : cumul_letteries_wellform' (B1 /\ B2) cumul_letteries)
: forall (z : nodes B2), node_is_letter z -> (restr_right cumul_letteries) z = true :=

  fun (z : B2) (H : node_is_letter z) => H_cumul_letteries_wellform (at_right B1 z) H
(*
Proof.
intros; eapply H_cumul_letteries_wellform; assumption.
Show Proof.
*).
Hint Unfold restr_right_wellform.
Hint Resolve restr_right_wellform.

(**/!\ OLD BAD, REPLACED BY restr_left_wellform
Lemma lem234 (B1 B2 : objects)
      (cumul_letteries : (nodes (B1 /\ B2)) -> bool) 
      (H_cumul_letteries_wellform' : cumul_letteries_wellform' (B1 /\ B2) cumul_letteries)
: cumul_letteries_wellform' B1 (restr_left cumul_letteries).
  
induction x; auto; intros; eapply H_cumul_letteries_wellform'; eauto.
Defined.
Hint Resolve lem234.
Print lem234.

Lemma lem234' (B1 B2 : objects)
      (cumul_letteries : (nodes (B1 /\ B2)) -> bool) 
      (H_cumul_letteries_wellform' : cumul_letteries_wellform' (B1 /\ B2) cumul_letteries)
: cumul_letteries_wellform' B2 (restr_right cumul_letteries).

  induction x; auto; intros; eapply H_cumul_letteries_wellform'; eauto.
Defined.
Hint Resolve lem234'.
**)

Lemma lem009900_post1  (A : objects) (H_none_object_is_letter : object_is_letter A -> Empty_set)
: object_is_tensor A.
  
  induction A; ((simpl in *; auto) || (elimtype Empty_set; apply H_none_object_is_letter; auto)).
Defined.
Hint Resolve lem009900_post1.

Lemma lem009900_post2 (A : objects) (x : nodes A) (H_none_node_is_letter : (node_is_letter x -> Empty_set))
: node_is_tensor x.

  induction x; ((simpl in *; auto) || (elimtype Empty_set; apply H_none_node_is_letter; auto)).
Defined.
Hint Resolve lem009900_post2.

Lemma next_in_cumul_letteries (B : objects)
      (cumul_letteries : nodes B -> bool)
      (H_cumul_letteries_wellform : cumul_letteries_wellform' B cumul_letteries)
      (H_cumul_letteries : cumul_letteries (self B) = false) 
: {x : nodes B & {y : nodes B & {y' : nodes B & lt_left_once x y * (lt_right_once x y' * ((forall x' : nodes B, lt_leftorright_eq x' x -> cumul_letteries x' = false) * ((cumul_letteries y = true) * (cumul_letteries y' = true))))}}}%type.

  induction B.
  * cut (cumul_letteries (self (letter l)) = true);
    [ intros Htemp; rewrite Htemp in H_cumul_letteries;  discriminate H_cumul_letteries 
    | apply H_cumul_letteries_wellform; simpl; auto
    ].
  * destruct (Sumbool.sumbool_of_bool (cumul_letteries (at_right _ (self B2)))) as [H_cumul_letteries_B2 | H_cumul_letteries_B2].
  - destruct (Sumbool.sumbool_of_bool (cumul_letteries (at_left (self B1) _))) as [H_cumul_letteries_B1 | H_cumul_letteries_B1].
    + split with (self (B1 /\ B2));
      split with (at_left (self B1) B2);
      split with (at_right B1 (self B2));
      split;
      [ auto
      | split;
        [ auto
        | split;
          [ intros x' [H_lt_leftorright_eq_x'_x | [H_lt_leftorright_eq_x'_x | H_lt_leftorright_eq_x'_x]];
            dependent destruction H_lt_leftorright_eq_x'_x;
            auto
          | auto
          ]
        ]
      ].
    + assert (xyy' : 
         {x : B1 &
         {y : B1 &
         {y' : B1 &
         (lt_left_once x y *
          (lt_right_once x y' *
           ((forall x' : nodes B1, lt_leftorright_eq x' x -> restr_left cumul_letteries x' = false) *
            ((restr_left cumul_letteries y = true) * 
             ((restr_left cumul_letteries y' = true))))))%type}}})
        by (apply IHB1; auto).
      destruct xyy' as (x & y & y' & xyy'_prop_1 & xyy'_prop_2 & xyy'_prop_3 & xyy'_prop_4 & xyy'_prop_5).
      split with (at_left x _);
        split with (at_left y _);
        split with (at_left y' _);
        split;
        [ auto
        | split;
          [ auto
          | split;
            [ intros x' [H_lt_leftorright_eq_x'_x | [H_lt_leftorright_eq_x'_x | H_lt_leftorright_eq_x'_x]];
              dependent destruction H_lt_leftorright_eq_x'_x;
              [ unfold restr_left in *; eauto
              | unfold restr_left in *; eauto
              | cut (lt_leftorright_eq x0 x) (*/!\ new name x0 from x' produced by dependent destruction H_lt_leftorright_eq_x'_x *);
                [ eauto
                | auto
                ] ..
              ]
            | auto
            ]
          ]
        ].
  - assert (xyy' : 
         {x : B2 &
         {y : B2 &
         {y' : B2 &
         (lt_left_once x y *
          (lt_right_once x y' *
           ((forall x' : nodes B2, lt_leftorright_eq x' x -> restr_right cumul_letteries x' = false) *
            ((restr_right cumul_letteries y = true) * 
             ((restr_right cumul_letteries y' = true))))))%type}}})
        by (apply IHB2; auto).
      destruct xyy' as (x & y & y' & xyy'_prop_1 & xyy'_prop_2 & xyy'_prop_3 & xyy'_prop_4 & xyy'_prop_5).
      split with (at_right _ x);
        split with (at_right _ y);
        split with (at_right _ y');
        split;
        [ auto
        | split;
          [ auto
          | split;
            [ intros x' [H_lt_leftorright_eq_x'_x | [H_lt_leftorright_eq_x'_x | H_lt_leftorright_eq_x'_x]];
              dependent destruction H_lt_leftorright_eq_x'_x;
              [ unfold restr_right in *; eauto
              | cut (lt_leftorright_eq x0 x) (*/!\ new name x0 from x' produced by dependent destruction H_lt_leftorright_eq_x'_x *);
                [ eauto
                | auto
                ]
              | unfold restr_right in *; eauto
              | cut (lt_leftorright_eq x0 x) (*/!\ new name x0 from x' produced by dependent destruction H_lt_leftorright_eq_x'_x *);
                [ eauto
                | auto
                ]
              ]
            | auto
            ]
          ]
        ].
Defined.
Hint Resolve next_in_cumul_letteries.

(**
(**/!\ OBSOLETE, REPLACED BY lengthn'' BELOW **)
Lemma lengthn'_specif (A : objects)
      (cumul_letteries : nodes A -> bool)
      (H_cumul_letteries_wellform : cumul_letteries_wellform' A cumul_letteries)
: {n : nat & prod (1 <= n) 
           (cumul_letteries (self A) = true <-> n = 1)}.

  induction A.
  - split with 1; split;
    [ auto
    | split; 
      [ intros; auto
      | intros; eapply H_cumul_letteries_wellform; simpl; eauto
      ]
    ].
  - destruct (Sumbool.sumbool_of_bool (cumul_letteries ((self (A1 /\ A2))))) as [H_cumul_letteries | H_cumul_letteries].
    + split with 1; (* intuition = *) split;
      [ auto
      | split; 
        [ intros; auto
        | intros; assumption
        ]
      ].
    + assert (H_cumul_letteries_wellform_restr_left : 
                cumul_letteries_wellform'  A1 (restr_left cumul_letteries))
        by auto.
      assert (H_cumul_letteries_wellform_restr_right : 
                cumul_letteries_wellform'  A2 (restr_right cumul_letteries))
        by auto.
      
      specialize IHA1 with (cumul_letteries := (restr_left cumul_letteries))
                             (1 := H_cumul_letteries_wellform_restr_left).
      destruct IHA1 as (IHA1_n & IHA1_prop1 & IHA1_prop2 & IHA1_prop3).
      specialize IHA2 with (cumul_letteries := (restr_right cumul_letteries))
                             (1 := H_cumul_letteries_wellform_restr_right).
      destruct IHA2 as (IHA2_n & IHA2_prop1 & IHA2_prop2 & IHA2_prop3).

      split with (IHA1_n + IHA2_n).
      split.
      * auto with zarith.
      * split;
        [ intros Htemp; rewrite Htemp in H_cumul_letteries; discriminate H_cumul_letteries
        | cut (1 + 1 <= IHA1_n + IHA2_n);
          [ intros; exfalso; auto with zarith
          | auto with zarith
          ]
        ].
Defined.
**)

(**/!\ REPLACE lengthn'_specif ABOVE **)
Fixpoint lengthn'' (A : objects)
      (cumul_letteries : nodes A -> bool)
      (H_cumul_letteries_wellform : cumul_letteries_wellform' A cumul_letteries) {struct A}
: nat.

Proof.
  destruct A.
  - exact 1.
  - destruct (Sumbool.sumbool_of_bool (cumul_letteries ((self (A1 /\ A2))))) as [H_cumul_letteries | H_cumul_letteries].
    + exact 1.
    +  pose (IHA1 := lengthn'' (A1) ((restr_left cumul_letteries))
                               (restr_left_wellform _ H_cumul_letteries_wellform)).
       pose (IHA2 := lengthn'' A2 ((restr_right cumul_letteries))
                               (restr_right_wellform _ H_cumul_letteries_wellform)).
       exact (IHA1 + IHA2).
Defined.
(* Hint Unfold lengthn''. /!\ COQ bug unfold fixpoints too much, and should fold any (fix funcname := ) into (funcname) *)

Lemma lem005400'' (A : objects)
      (cumul_letteries : nodes A -> bool) 
      (H_cumul_letteries_wellform : cumul_letteries_wellform' A cumul_letteries)
: 1 <= lengthn'' cumul_letteries H_cumul_letteries_wellform.

  induction A;
  [ auto with zarith
  | simpl;
    destruct (Sumbool.sumbool_of_bool (cumul_letteries ((self (A1 /\ A2))))) as [H_cumul_letteries | H_cumul_letteries];
    specialize IHA1 with (cumul_letteries := restr_left cumul_letteries) (H_cumul_letteries_wellform := restr_left_wellform _ H_cumul_letteries_wellform);
    specialize IHA2 with (cumul_letteries := restr_right cumul_letteries) (H_cumul_letteries_wellform := restr_right_wellform _ H_cumul_letteries_wellform);
    auto with zarith
  ].
Defined.
Hint Resolve lem005400''.

Lemma lem005400''_post (A : objects)
      (cumul_letteries : nodes A -> bool) 
      (H_cumul_letteries_wellform : cumul_letteries_wellform' A cumul_letteries)
: (cumul_letteries (self A) = true <-> lengthn'' cumul_letteries H_cumul_letteries_wellform = 1).

  (*notice that these proof commands below is copy-paste from specif part of old lengthn'_specif above*)

  induction A.
  - simpl lengthn'';
    split; 
    [ intros; auto
    | intros; eapply H_cumul_letteries_wellform; simpl; eauto
    ].
  - simpl lengthn'';
    destruct (Sumbool.sumbool_of_bool (cumul_letteries ((self (A1 /\ A2))))) as [H_cumul_letteries | H_cumul_letteries].
    + split; 
      [ intros; auto
      | intros; assumption
      ].
    + specialize IHA1 with (cumul_letteries := restr_left cumul_letteries) (H_cumul_letteries_wellform := restr_left_wellform _ H_cumul_letteries_wellform);
      specialize IHA2 with (cumul_letteries := restr_right cumul_letteries) (H_cumul_letteries_wellform := restr_right_wellform _ H_cumul_letteries_wellform);
      split;
      [ intros Htemp; rewrite Htemp in H_cumul_letteries; discriminate H_cumul_letteries
      | cut (1 + 1 <= (lengthn'' (restr_left cumul_letteries) (restr_left_wellform _ H_cumul_letteries_wellform)) + (lengthn'' (restr_right cumul_letteries) (restr_right_wellform _ H_cumul_letteries_wellform)));
        [ intros; exfalso; auto with zarith
        | cut ( 1 <= lengthn'' (restr_left cumul_letteries)
                               (restr_left_wellform cumul_letteries H_cumul_letteries_wellform));
          cut ( 1 <= lengthn'' (restr_right cumul_letteries)
                               (restr_right_wellform cumul_letteries H_cumul_letteries_wellform));
          auto with zarith
        ]
      ].
Defined.
Hint Resolve lem005400''_post.


(*/!\ COQ BUG? auto is not so good at using the apply which actually decompose the conclusion when tuple type, 
even/same if apply alone do decompose the conclusion when tuple type *)
Lemma lem005400''_post' (A : objects)
      (cumul_letteries : nodes A -> bool) 
      (H_cumul_letteries_wellform : cumul_letteries_wellform' A cumul_letteries)
: (cumul_letteries (self A) = true -> lengthn'' cumul_letteries H_cumul_letteries_wellform = 1).

(*Fail progress auto.*)
apply lem005400''_post; assumption.
Defined.
Hint Resolve lem005400''_post'.
Lemma lem005400''_post'' (A : objects)
      (cumul_letteries : nodes A -> bool) 
      (H_cumul_letteries_wellform : cumul_letteries_wellform' A cumul_letteries)
: (lengthn'' cumul_letteries H_cumul_letteries_wellform = 1 -> cumul_letteries (self A) = true).

apply lem005400''_post; assumption.
Defined.
Hint Resolve lem005400''_post''.

Lemma lem005400''_post2 (A : objects)
      (cumul_letteries1 : nodes A -> bool)
      (H_cumul_letteries_wellform1 : cumul_letteries_wellform' A cumul_letteries1)
      (cumul_letteries2 : nodes A -> bool)
      (H_cumul_letteries_wellform2 : cumul_letteries_wellform' A cumul_letteries2)
      (H_forall_same : forall x : nodes A, cumul_letteries1 x = cumul_letteries2 x)
: lengthn'' cumul_letteries1 H_cumul_letteries_wellform1 = lengthn'' cumul_letteries2 H_cumul_letteries_wellform2.

  induction A.
  - simpl (*not lacked*); reflexivity.
  - simpl.
    assert (H_forall_same_self : cumul_letteries1 (self (A1 /\ A2))  =  cumul_letteries2 (self (A1 /\ A2))  ) by auto (*(intros; apply H_forall_same)*).
    assert (H_forall_same_A1: forall x : nodes A1, cumul_letteries1 (at_left x A2) = cumul_letteries2 (at_left x A2)) by auto (*(intros; apply H_forall_same)*).
    assert (H_forall_same_A2: forall x : nodes A2, cumul_letteries1 (at_right A1 x) = cumul_letteries2 (at_right A1 x)) by auto (*(intros; apply H_forall_same)*).
    destruct (Sumbool.sumbool_of_bool (cumul_letteries1 (self (A1 /\ A2)))) as [H_cumul_letteries1_self | H_cumul_letteries1_self].
    + destruct (Sumbool.sumbool_of_bool (cumul_letteries2 (self (A1 /\ A2)))) as [H_cumul_letteries2_self | H_cumul_letteries2_self].
      * reflexivity.
      * rewrite H_cumul_letteries1_self, H_cumul_letteries2_self in H_forall_same_self;
        discriminate H_forall_same_self. 
    + destruct (Sumbool.sumbool_of_bool (cumul_letteries2 (self (A1 /\ A2)))) as [H_cumul_letteries2_self | H_cumul_letteries2_self].
      * rewrite H_cumul_letteries1_self, H_cumul_letteries2_self in H_forall_same_self;
        discriminate H_forall_same_self.
      * autounfold.
        (* ALT: erewrite IHA1; eauto. Defined. *)
        erewrite IHA1, IHA2;
          [ reflexivity 
          | assumption .. 
          ].
Defined.

(**
(**/!\ OBSOLETE, REPLACED BY lengthn'' ABOVE **)
Definition lengthn' A cu wf := projT1 (@lengthn'_specif A cu wf).
(**/!\ OBSOLETE, REPLACED BY lengthn'' ABOVE **)
Lemma lem005400' (A : objects)
      (cumul_letteries : nodes A -> bool) 
      (H_cumul_letteries_wellform : cumul_letteries_wellform' A cumul_letteries)
: 1 <= lengthn' cumul_letteries H_cumul_letteries_wellform.

  exact (fst (projT2 (@lengthn'_specif A cumul_letteries H_cumul_letteries_wellform) ) ).
Defined.
Hint Resolve lem005400'.
**)

Lemma lem010000 (A B : objects) (x y : nodes A)
:       (lt_leftorright_eq (at_left x B) (at_left y B))
-> lt_leftorright_eq x y. 
  intros [H_lt_leftorright_eq | [H_lt_leftorright_eq | H_lt_leftorright_eq]];
  dependent destruction H_lt_leftorright_eq; auto.
Defined.
Hint Resolve lem010000.

Lemma lem010100 (A B : objects) (x y : nodes A)
:       (lt_leftorright_eq (at_right B x) (at_right B y))
-> lt_leftorright_eq x y.
  intros [H_lt_leftorright_eq | [H_lt_leftorright_eq | H_lt_leftorright_eq]];
  dependent destruction H_lt_leftorright_eq; auto.
Defined.
Hint Resolve lem010100.

Lemma lem010200 (B : objects) (x : nodes B)
:       (lt_leftorright_eq (self B) x).

destruct x; auto.
Defined.
Hint Resolve lem010200.

Lemma lem010300 (B C : objects) (x : nodes (B /\ C))
 (H_lt_leftorright_eq_self : (lt_leftorright_eq (self (B /\ C)) x))
: (eq (self (B /\ C)) x) + ((lt_leftorright_eq (at_left (self B) C) x) + (lt_leftorright_eq (at_right B (self C)) x)).
 
dependent induction x;
decompose sum H_lt_leftorright_eq_self;
eauto.
Defined.
Hint Resolve lem010300.


(** HERE **)

Lemma lem010400 (A : objects) (x : nodes A)
: (eq (self A) x) + ((lt_left (self A) x) + (lt_right (self A) x)).

induction x; auto.
Defined.
Hint Resolve lem010400.

Lemma lem010500 (A : objects) (x y : nodes A)
      (H_lt_left_once : lt_left_once x y)
: forall (z : nodes A) (H_lt_left : lt_left x z)
  , lt_leftorright_eq y z.

induction H_lt_left_once; intros; dependent destruction H_lt_left; auto.
Defined.
Hint Resolve lem010500.

Lemma lem010600 (A : objects) (x y : nodes A)
      (H_lt_right_once : lt_right_once x y)
: forall (z : nodes A) (H_lt_right : lt_right x z)
  , lt_leftorright_eq y z.

induction H_lt_right_once; intros; dependent destruction H_lt_right; auto.
Defined.
Hint Resolve lem010600.


Lemma lem010700 (B A : objects) (f : arrows_assoc B A) (x y y' : nodes B)
      (xyy'_prop_1 : lt_left_once x y)
      (xyy'_prop_1' : lt_left_once (f x) (f y))
      (xyy'_prop_2 : lt_right_once x y')   
      (xyy'_prop_2' : lt_right_once (f x) (f y')) (**/!\ WE DO HAVE lt_right_once AFTER nodal_multi_bracket on A to get A',  thefore the hypothesis here is lt_right_once, and everything is symmetric: left/right, f/(rev f) **)
      (H_node_is_lettery : node_is_lettery f y)
      (H_node_is_lettery' : node_is_lettery f y')
: (forall z : B, lt_leftorright_eq x z -> lt_leftorright_eq (f x) (f z)) (* =: node_is_lettery_half f x *).

  destruct H_node_is_lettery as [H_node_is_lettery _];
  destruct H_node_is_lettery' as [H_node_is_lettery' _].
  intros z [H_lt_leftorright_eq_x_z | [H_lt_leftorright_eq_x_z | H_lt_leftorright_eq_x_z]].
  + subst z; auto.
  + cut (lt_leftorright_eq y z);
    [ cut (lt_leftorright_eq (f x) (f y)) ; 
      [ intros; eapply lem00410' with (y:=(f y)); auto (* /!\ lem00410' cause problems.. this is not enough:  intros J1 J2; specialize H_node_is_lettery with (x:=z)(1:=J2);  eauto*)
      | auto 
      ]
    | eapply lem010500 with (x:=x); auto (* eauto  *)
    ].
  + cut (lt_leftorright_eq y' z);
    [ cut (lt_leftorright_eq (f x) (f y')) ; 
      [ intros; eapply lem00410' with (y:=(f y')); auto (* /!\ lem00410' cause problems.. this is not enough:  intros J1 J2; specialize H_node_is_lettery' with (x:=z)(1:=J2); eauto*)
      | auto 
      ]
    | eapply lem010600 with (x:=x); auto (* eauto *)
    ].
Defined.
Hint Resolve lem010700.

Lemma lem010800 (B A : objects) (f : arrows_assoc B A) (x y y' : nodes B)
      (xyy'_prop_1 : lt_left_once x y)
      (xyy'_prop_1' : lt_left_once (f x) (f y))
      (xyy'_prop_2 : lt_right_once x y')   
      (xyy'_prop_2' : lt_right_once (f x) (f y')) (**/!\ WE DO HAVE lt_right_once AFTER nodal_multi_bracket on A to get A',  thefore the hypothesis here is lt_right_once, and everything is symmetric: left/right, f/(rev f) **)
      (H_node_is_lettery : node_is_lettery f y)
      (H_node_is_lettery' : node_is_lettery f y')
:  node_is_lettery f x.

  split.
  - eapply lem010700; eauto.
  - assert (H_node_is_lettery_rev : node_is_lettery (rev f) (f y)) by auto.
    assert (H_node_is_lettery'_rev : node_is_lettery (rev f) (f y')) by auto.
    replace x with ((rev f) (f x)) in xyy'_prop_1, xyy'_prop_2 by auto;
      replace y with ((rev f) (f y)) in xyy'_prop_1 by auto;
      replace y' with ((rev f) (f y')) in  xyy'_prop_2 by auto;
      intros; eapply lem010700 with (f:=(rev f)); eauto.
Defined.
Hint Resolve lem010800.


(**/!\ THESE OLD lem010400 BELOW WONT WORK BY induction xyy'_prop_1 /!\

(*
Lemma lem010400 (B A : objects) (f : arrows_assoc B A) (x y y' : nodes B)
      (xyy'_prop_1 : lt_left_once x y)
: forall      (xyy'_prop_1' : lt_left_once (f x) (f y))
      (xyy'_prop_2 : lt_right x y')   (**/!\ WE DO HAVE lt_right_once AFTER nodal_multi_bracket on A to get A',
 thefore the hypothesis here is lt_right_once, and everything is symmetric: left/right, f/(rev f) **)
      (xyy'_prop_2' : lt_right (f x) (f y'))
      (H_node_is_lettery : node_is_lettery f y)
      (H_node_is_lettery' : node_is_lettery f y')
, node_is_lettery f x. *)

Lemma lem010400 (B A : objects) (f : arrows_assoc B A) (x y y' : nodes B)

      (xyy'_prop_1' : lt_left_once (f x) (f y))
      (xyy'_prop_2 : lt_right_once x y')   (**/!\ WE DO HAVE lt_right_once AFTER nodal_multi_bracket on A to get A',
 thefore the hypothesis here is lt_right_once, and everything is symmetric: left/right, f/(rev f) **)
      (xyy'_prop_2' : lt_right_once (f x) (f y'))
      (H_node_is_lettery : node_is_lettery f y)
      (H_node_is_lettery' : node_is_lettery f y')
      (xyy'_prop_1 : lt_left_once x y)
: node_is_lettery f x.


  split.
  - destruct H_node_is_lettery as [H_node_is_lettery _];
    destruct H_node_is_lettery' as [H_node_is_lettery' _].
    induction xyy'_prop_1; dependent destruction xyy'_prop_2.
    + intros t;
        assert (H_lt_leftorright_eq_t : (eq (self (B /\ C)) t) + ((lt_leftorright_eq (at_left (self B) C) t) + (lt_leftorright_eq (at_right B (self C)) t))) by auto.
      destruct H_lt_leftorright_eq_t as [ H_lt_leftorright_eq_t | [ H_lt_leftorright_eq_t | H_lt_leftorright_eq_t ]].
      * subst t; auto.
      * cut (lt_leftorright_eq (f (self (B /\ C))) (f (at_left (self B) C)));
          [ | auto ].
        intros. eauto.
        Show Existentials.
      * cut (lt_leftorright_eq (f (self (B /\ C))) (f (at_right B (self C))));
          [ | auto ].
        intros. eauto.
        Show Existentials.
    + intuition eauto.
*)


Lemma lem010900 (A : objects) (x y : nodes A)
      (xyy'_prop_1 : lt_left_once x y)
: forall  (y' : nodes A) (xyy'_prop_2 : lt_right_once x y')   
  , object_at_node x = ((object_at_node y) /\ (object_at_node y')).

induction xyy'_prop_1; intros; dependent destruction xyy'_prop_2; simpl in *; auto.
(**as usual, one attempt only :D *)
Defined.
Hint Resolve lem010900.
Hint Rewrite lem010900 using eauto. (* :( *)
Print Rewrite HintDb core.


Lemma lem011000 (B A : objects) (f : arrows_assoc B A) (x y y' : nodes B)
      (xyy'_prop_1 : lt_left_once x y)
      (xyy'_prop_1' : lt_left_once (f x) (f y))
      (xyy'_prop_2 : lt_right_once x y')   
      (xyy'_prop_2' : lt_right_once (f x) (f y'))
      (H_node_is_lettery : object_at_node y = object_at_node (f y))
      (H_node_is_lettery' : object_at_node y' = object_at_node (f y'))
: object_at_node x = object_at_node (f x).

(* /!\ ?? :( autorewrite * with core using eauto. *)
replace (object_at_node x) with (object_at_node y /\ object_at_node y') by (symmetry; eauto).
replace (object_at_node (f x)) with (object_at_node (f y) /\ object_at_node (f y')) by (symmetry; eauto).
rewrite H_node_is_lettery; rewrite H_node_is_lettery'; reflexivity.
Defined.
Hint Resolve lem011000.
Hint Rewrite lem011000 using eauto.

(* FOR VERSION HISTORY, THIS IS THE OLD PLACE of 
Definition restr_left_wellform (A1 A2 : objects)
Definition restr_right_wellform (A1 A2 : objects)
*)

(* lengthn'' shall be fixpoint entry and not lemma with opaque/internal induction, for this next lemma lem011100 to be at once *)
Lemma lem011100 (A1 A2 : objects)
      (cumul_letteries : nodes (A1 /\ A2) -> bool)
      (H_cumul_letteries_wellform : cumul_letteries_wellform' (A1 /\ A2) cumul_letteries)
      (H_cumul_letteries_self_false : cumul_letteries (self _) = false)
: lengthn'' cumul_letteries H_cumul_letteries_wellform = 
  lengthn'' (restr_left cumul_letteries) (restr_left_wellform _ H_cumul_letteries_wellform) + 
  lengthn'' (restr_right cumul_letteries) (restr_right_wellform _ H_cumul_letteries_wellform).

  simpl lengthn'' at 1;
  rewrite H_cumul_letteries_self_false;
  reflexivity.
Defined.

Definition more_cumul_letteries (B : objects)
      (cumul_letteries : nodes B -> bool)
      (H_cumul_letteries_wellform : cumul_letteries_wellform' B cumul_letteries)
      (x : nodes B)
      (H_cumul_letteries_x_false : (forall x' : nodes B, lt_leftorright_eq x' x -> cumul_letteries x' = false))
: { cumul_letteries' : nodes B -> bool &
    { H_cumul_letteries_wellform' : cumul_letteries_wellform' B cumul_letteries' &
      (lengthn'' cumul_letteries' H_cumul_letteries_wellform' < lengthn'' cumul_letteries H_cumul_letteries_wellform) } }.

  pose  (fun x0 : B =>
           if nodes_eq_dec x0 x 
           then true 
           else cumul_letteries x0) as cumul_letteries';
  split with cumul_letteries'.
  (* (** proof term of *)
  intros x0;
  destruct (nodes_eq_dec x0 x) as [Heq_x0_x | Hneq_x0_x];
  [ exact true
  | exact (cumul_letteries x0)
  ]. Show Proof.
   *)

  pose (fun x0 : B =>
          if nodes_eq_dec x0 x as s0
             return (node_is_letter x0 -> (if s0 then true else cumul_letteries x0) = true)
          then fun _ : node_is_letter x0 => eq_refl
          else H_cumul_letteries_wellform x0) as H_cumul_letteries_wellform';
    split with H_cumul_letteries_wellform'.
  (* (** proof term of *)
intros x0; subst cumul_letteries'; simpl.
destruct (nodes_eq_dec x0 x) as [Heq_x0_x | Hneq_x0_x]; [auto | eauto].
Show Proof.
   *)

  assert (H_cumul_letteries_x_false_immediate : cumul_letteries x = false) by auto.
  assert (H_node_is_letter_none_x : node_is_letter x -> Empty_set)
    by (intros;
        cut (cumul_letteries x = true);
        [
          intros Htemp; rewrite Htemp in H_cumul_letteries_x_false_immediate;
          discriminate H_cumul_letteries_x_false_immediate
        | auto
       ]).
  assert (H_node_is_tensor_x : node_is_tensor x) by auto.

  assert (H_cumul_letteries_self_false_immediate : cumul_letteries (self B) = false) by auto.

  induction x.
  - simpl in H_node_is_tensor_x;
    destruct H_node_is_tensor_x;
    simpl lengthn'';
    rewrite H_cumul_letteries_x_false_immediate;
    simpl.
    cut (1 <= lengthn'' (restr_left cumul_letteries)
                        (restr_left_wellform cumul_letteries H_cumul_letteries_wellform));
      cut (1 <= lengthn'' (restr_right cumul_letteries)
                          (restr_right_wellform cumul_letteries H_cumul_letteries_wellform));
      auto with zarith.

  - simpl lengthn''.
    replace (cumul_letteries' (self (A /\ B))) with (cumul_letteries (self (A /\ B)))
      by reflexivity.
    rewrite H_cumul_letteries_self_false_immediate.
    simpl.

    assert ( Htemp: (restr_right cumul_letteries') = (restr_right cumul_letteries) )
      by (autounfold; reflexivity).
    clear Htemp.

    assert (H_eq_right : lengthn'' (restr_right cumul_letteries')
                       (restr_right_wellform cumul_letteries' H_cumul_letteries_wellform') =
             lengthn'' (restr_right cumul_letteries)
                       (restr_right_wellform cumul_letteries H_cumul_letteries_wellform) )
      by (autounfold; reflexivity).

    cut ( lengthn'' (restr_left cumul_letteries')
                    (restr_left_wellform cumul_letteries' H_cumul_letteries_wellform') <
          lengthn'' (restr_left cumul_letteries)
                    (restr_left_wellform cumul_letteries H_cumul_letteries_wellform) );
      [ auto with zarith
      | idtac ].

    specialize IHx with (cumul_letteries := (restr_left cumul_letteries))
                          (H_cumul_letteries_wellform := (restr_left_wellform cumul_letteries H_cumul_letteries_wellform)).
    pose ( fun x0 : A =>
             if nodes_eq_dec x0 x then true else restr_left cumul_letteries x0 ) as restr_left_cumul_letteries'.
    pose ( fun x0 : A =>
             if nodes_eq_dec x0 x as s0
                return
                (node_is_letter x0 ->
                 (if s0 then true else restr_left cumul_letteries x0) = true)
             then fun _ : node_is_letter x0 => eq_refl
             else
               restr_left_wellform cumul_letteries H_cumul_letteries_wellform x0 ) as restr_left_wellform_H_cumul_letteries_wellform'.

    assert (H_eq_left_simpl : lengthn'' (restr_left cumul_letteries')
                       (restr_left_wellform cumul_letteries' H_cumul_letteries_wellform') = 
             lengthn'' (restr_left_cumul_letteries')
                       (restr_left_wellform_H_cumul_letteries_wellform') ).
    { 
      unfold restr_left_cumul_letteries';
      unfold restr_left_wellform_H_cumul_letteries_wellform';
      autounfold.
      unfold cumul_letteries'.
      unfold H_cumul_letteries_wellform'.  
      (*/!\ NEXT LEMMA PROVE lengthn'' NON-VARIANT AFTER
      IF POINT-WISE SAME cumul_letteries (PARTICULAR FUNTIONAL EXTENSIONALITY).
 ALT: IF POINT-WISE SAME prop_cumul_letteries (PARTICULAR PROPOSITIONAL EXTENSIONALITY).
 HERE: nodes_eq_dec (at_left _ _) (at_left _ _)
       node_is_letter (at_left _ _)
       fun (z : A) (H1 : node_is_letter z) => _ H1
       fun H1 : node_is_letter x0 => _ H1                                               *)
      (*
  ============================
   lengthn''
     (fun z : A =>
      if nodes_eq_dec (at_left z B) (at_left x B)
      then true
      else cumul_letteries (at_left z B))
     (fun (z : A) (H1 : node_is_letter z) =>
      (if nodes_eq_dec (at_left z B) (at_left x B) as s0
        return
          (node_is_letter (at_left z B) ->
           (if s0 then true else cumul_letteries (at_left z B)) = true)
       then fun _ : node_is_letter (at_left z B) => eq_refl
       else H_cumul_letteries_wellform (at_left z B)) H1) =
   lengthn''
     (fun x0 : A =>
      if nodes_eq_dec x0 x then true else cumul_letteries (at_left x0 B))
     (fun x0 : A =>
      if nodes_eq_dec x0 x as s0
       return
         (node_is_letter x0 ->
          (if s0 then true else cumul_letteries (at_left x0 B)) = true)
      then fun _ : node_is_letter x0 => eq_refl
      else
       fun H1 : node_is_letter x0 =>
       H_cumul_letteries_wellform (at_left x0 B) H1)
       *)

      assert (H_forall_same : forall t, (fun z : A =>
                                           if nodes_eq_dec (at_left z B) (at_left x B)
                                           then true
                                           else cumul_letteries (at_left z B)) t =
                                        (fun x0 : A =>
                                           if nodes_eq_dec x0 x then true else cumul_letteries (at_left x0 B)) t).
      {
        intros.
        destruct (nodes_eq_dec (at_left t B) (at_left x B)) as [H_dec_at_left_t_x | H_dec_at_left_t_x];
          destruct (nodes_eq_dec t x) as [H_dec_t_x  | H_dec_t_x];
          [ reflexivity
          | dependent destruction H_dec_at_left_t_x; exfalso; apply H_dec_t_x; reflexivity
          | destruct H_dec_t_x; exfalso; apply H_dec_at_left_t_x; reflexivity
          | reflexivity ].
      }

      apply lem005400''_post2; assumption (* exact H_forall_same *).

    (**HOW USEFUL IS THIS LEMMA INSTEAD
Lemma lem011100_pre1 (A B : objects)
      (x y : nodes A)
: if nodes_eq_dec (at_left x B) (at_left y B) 
  then {ll : x = y & nodes_eq_dec x y = left ll}
  else {ll : x <> y & nodes_eq_dec x y = right ll} .

destruct (nodes_eq_dec (at_left x B) (at_left y B)) as [ll | ll];
destruct (nodes_eq_dec x y) as [pp | pp].
 esplit; reflexivity.
 dependent destruction ll. exfalso; apply pp; reflexivity. 
 destruct pp. exfalso; apply ll; reflexivity. 
 esplit; reflexivity.
Defined. **)
    }

    {
      rewrite H_eq_left_simpl.
      apply IHx.
      + unfold restr_left; auto.
      + assumption (* exact H_cumul_letteries_x_false_immediate. *). (* these little at-once come from the little extra assumptions to prepare before induction x *)
      + assumption (* exact H_node_is_letter_none_x. *). (* these little at-once come from the little extra assumptions to prepare before induction x *)
      + assumption (* exact H_node_is_tensor_x. *).  (* these little at-once come from the little extra assumptions to prepare before induction x *)
      + unfold restr_left; auto.
    }

  - simpl lengthn''.
    replace (cumul_letteries' (self (A /\ B))) with (cumul_letteries (self (A /\ B)))
      by reflexivity.
    rewrite H_cumul_letteries_self_false_immediate.
    simpl.

    assert ( Htemp: (restr_left cumul_letteries') = (restr_left cumul_letteries) )
      by (autounfold; reflexivity).
    clear Htemp.

    assert (H_eq_left : lengthn'' (restr_left cumul_letteries')
                       (restr_left_wellform cumul_letteries' H_cumul_letteries_wellform') =
             lengthn'' (restr_left cumul_letteries)
                       (restr_left_wellform cumul_letteries H_cumul_letteries_wellform) )
      by (autounfold; reflexivity).

    cut ( lengthn'' (restr_right cumul_letteries')
                    (restr_right_wellform cumul_letteries' H_cumul_letteries_wellform') <
          lengthn'' (restr_right cumul_letteries)
                    (restr_right_wellform cumul_letteries H_cumul_letteries_wellform) );
      [ auto with zarith
      | idtac ].

    specialize IHx with (cumul_letteries := (restr_right cumul_letteries))
                          (H_cumul_letteries_wellform := (restr_right_wellform cumul_letteries H_cumul_letteries_wellform)).
    pose ( fun x0 : B =>
             if nodes_eq_dec x0 x then true else restr_right cumul_letteries x0 ) as restr_right_cumul_letteries'.
    pose ( fun x0 : B =>
             if nodes_eq_dec x0 x as s0
                return
                (node_is_letter x0 ->
                 (if s0 then true else restr_right cumul_letteries x0) = true)
             then fun _ : node_is_letter x0 => eq_refl
             else
               restr_right_wellform cumul_letteries H_cumul_letteries_wellform x0 ) as restr_right_wellform_H_cumul_letteries_wellform'.

    assert (H_eq_right_simpl : lengthn'' (restr_right cumul_letteries')
                       (restr_right_wellform cumul_letteries' H_cumul_letteries_wellform') = 
             lengthn'' (restr_right_cumul_letteries')
                       (restr_right_wellform_H_cumul_letteries_wellform') ).
    { 
      unfold restr_right_cumul_letteries';
      unfold restr_right_wellform_H_cumul_letteries_wellform';
      autounfold.
      unfold cumul_letteries'.
      unfold H_cumul_letteries_wellform'.  

      assert (H_forall_same : forall t, (fun z : B =>
                                           if nodes_eq_dec (at_right A z) (at_right A x)
                                           then true
                                           else cumul_letteries (at_right A z)) t =
                                        (fun x0 : B =>
                                           if nodes_eq_dec x0 x then true else cumul_letteries (at_right A x0)) t).
      {
        intros.
        destruct (nodes_eq_dec (at_right A t) (at_right A x)) as [H_dec_at_left_t_x | H_dec_at_left_t_x];
          destruct (nodes_eq_dec t x) as [H_dec_t_x  | H_dec_t_x];
          [ reflexivity
          | dependent destruction H_dec_at_left_t_x; exfalso; apply H_dec_t_x; reflexivity
          | destruct H_dec_t_x; exfalso; apply H_dec_at_left_t_x; reflexivity
          | reflexivity ].
      }

      apply lem005400''_post2; assumption (* exact H_forall_same *).
    }

    {
      rewrite H_eq_right_simpl.
      apply IHx.
      + unfold restr_right; auto.
      + assumption (* exact H_cumul_letteries_x_false_immediate. *). (* these little at-once come from the little extra assumptions to prepare before induction x *)
      + assumption (* exact H_node_is_letter_none_x. *). (* these little at-once come from the little extra assumptions to prepare before induction x *)
      + assumption (* exact H_node_is_tensor_x. *).  (* these little at-once come from the little extra assumptions to prepare before induction x *)
      + unfold restr_right; auto.
    }
Defined.
Hint Resolve more_cumul_letteries.




(** MAIN LEMMA **)

(* STEPS OF PROOF OF COMPLETENESS LEMMA lem005700

      (xyy'_prop_1 : lt_left_once x y)
      (xyy'_prop_2 : lt_right_once x y')   
      (xyy'_prop_1' : lt_left_once (f x) (f y))
      (H_lt_right_fx_fy' : lt_right (f x) (f y'))
=============
      (xyy'_prop_1' : lt_left_once (f' (f x)) (f' (f y))) by one multi_bra lem
      (xyy'_prop_2' : lt_right_once (f' (f x)) (f' (f y'))) by one multi_bra lem
      (H_node_is_lettery_y : node_is_lettery f y) by already auto xyy'_prop_4'
      (H_node_is_lettery_y' : node_is_lettery f y') by already auto xyy'_prop_5' 
      (H_object_at_node_y : object_at_node y = object_at_node (f' (f y)) by eq trans and one multi_bra lem and one 2-assumption H_object_at_node xyy'_prop_4)
      (H_object_at_node_y' : object_at_node y' = object_at_node (f' (f y')) by eq trans and one multi_bra lem and one 2-assumption H_object_at_node xyy'_prop_5)

      (H_node_is_lettery_x : node_is_lettery (com_assoc f f') x)
      (H_object_at_node_x : object_at_node x = object_at_node (f' (f x))

      (H_cumul_B : forall x y : B, lt_right x y -> lt_right (f' (f x)) (f' (f y)))
*)

Lemma lem005700 (B : objects) (len : nat) : 
  forall (cumul_letteries : nodes B -> bool)
         (H_cumul_letteries_wellform : cumul_letteries_wellform' B cumul_letteries)
         (H_cumul_letteries_satur : forall y : nodes B, cumul_letteries y = true 
                                                        -> forall z : nodes B, lt_leftorright_eq y z -> cumul_letteries z = true)
         (H_len : lengthn'' cumul_letteries H_cumul_letteries_wellform <= len),
  forall (A : objects) (f : arrows_assoc B A)
         (H_node_is_lettery : forall x : nodes B, cumul_letteries x = true -> node_is_lettery f x)
         (H_object_at_node : forall x : nodes B, cumul_letteries x = true -> object_at_node x = object_at_node (f x))
         (H_cumul_B : forall x y : nodes B, lt_right x y -> lt_right (f x) (f y))
  , arrows A B.

  destruct len.
  - intros; cut (1 <= lengthn'' cumul_letteries H_cumul_letteries_wellform) ; [ intros; exfalso; auto with zarith | auto ].
  - induction len.
    + intros.
      cut (lengthn'' cumul_letteries H_cumul_letteries_wellform = 1);
        [ idtac
        | cut (1 <= lengthn'' cumul_letteries H_cumul_letteries_wellform);
          auto with zarith
        ].
      intros.

      (*same below (H_cumul_letteries_selfB : cumul_letteries (self B) = true)*)
      assert (H_cumul_letteries_selfB : cumul_letteries (self B) = true) by eauto. 
      specialize H_object_at_node with (x:=self _) (1:=H_cumul_letteries_selfB).
      (*old commands now*)
      simpl in H_object_at_node.
      assert (H_lengthl_at_node : lengthl B = lengthl (object_at_node (f (self B)))) 
        by (f_equal; assumption).
      replace (lengthl B) with (lengthl A) in H_lengthl_at_node by (symmetry; auto).
      replace (f (self B)) with (self A) in H_object_at_node by (symmetry; auto).
      simpl in H_object_at_node;
        subst B.
      exact (unitt A).
    + intros.
      destruct (Sumbool.sumbool_of_bool (cumul_letteries (self B))) as [H_cumul_letteries_selfB | H_cumul_letteries_selfB].
      * (*same below (H_cumul_letteries_selfB : cumul_letteries (self B) = true)*)
        specialize H_object_at_node with (x:=self _) (1:=H_cumul_letteries_selfB).
        simpl in H_object_at_node.
        assert (H_lengthl_at_node : lengthl B = lengthl (object_at_node (f (self B)))) 
          by (f_equal; assumption).
        replace (lengthl B) with (lengthl A) in H_lengthl_at_node by (symmetry; auto).
        replace (f (self B)) with (self A) in H_object_at_node by (symmetry; auto).
        simpl in H_object_at_node;
          subst B.
        exact (unitt A).

      * (*same below (H_cumul_letteries_selfB : cumul_letteries (self B) = false)*)
        { destruct (next_in_cumul_letteries (cumul_letteries)
                                            (H_cumul_letteries_wellform)
                                            (H_cumul_letteries_selfB))
            as (x & y & y' & H_lt_left_once_x_y & H_lt_right_once_x_y' & H_cumul_letteries_x_false & H_cumul_letteries_y_true & H_cumul_letteries_y'_true).
(*            as (x & y & y' & xyy'_prop_1 & xyy'_prop_2 & xyy'_prop_3 & xyy'_prop_4 & xyy'_prop_5).*)

          assert (H_node_is_lettery_y : node_is_lettery f y ) by auto. (*xyy'_prop_4'*)
          assert (H_node_is_lettery_y' : node_is_lettery f y' ) by auto. (*xyy'_prop_5'*)
          assert (H_lt_left_once_fx_fy : lt_left_once (f x) (f y)) by auto (*using H_cumul_B*). (*xyy'_prop_1'*)
          assert (H_lt_right_fx_fy' : lt_right (f x) (f y')) by auto.
          assert (H_lt_right_once_almost_fx_fy' (*H_lem009800*) : (forall fw : nodes A, lt_right fw (f y') -> lt_right (f x) fw -> Empty_set)) by (apply lem009800; auto).
          
          (* it is better to dependent destruction (H_lt_right : lt_right (self E) fy'_loc) ,
             directly without node_is_tensor, locally, instead of
             (*assert (H_nit_fx : node_is_tensor (f x)) by eauto.*) 
          Lemma lem888 (A : objects) (x y : nodes A) (H_lt_right: lt_right x y)
          : node_is_tensor x.
            induction H_lt_right; simpl in *; auto.
          Defined.
          Hint Resolve lem888.
          *)

          (**  (**loc_all TOO GENERAL*)
          Lemma loc_all_rev (A : objects) (x : nodes A): nodes (object_at_node x) -> {y : nodes A & lt_leftorright_eq x y}.
            induction x.
            - intros y; split with y. auto.
            - intros y. destruct (IHx y) as (IHx_y & IHx_prop). split with ( at_left IHx_y B ). auto.
            - intros y. destruct (IHx y) as (IHx_y & IHx_prop). split with ( at_right A IHx_y ). auto.
          Defined.
          Lemma loc_all (A : objects) (x : nodes A): {y : nodes A & lt_leftorright_eq x y} -> nodes (object_at_node x).
            
            intros H_y; destruct H_y as (y & H_lt_leftorright_eq).
            destruct H_lt_leftorright_eq as [H_lt_leftorright_eq | [H_lt_leftorright_eq | H_lt_leftorright_eq]].
            - rewrite H_lt_leftorright_eq; exact (self (object_at_node y)).
            - induction H_lt_leftorright_eq.
              + exact (at_left z C).
              + exact IHH_lt_leftorright_eq.
              + exact IHH_lt_leftorright_eq.
            - induction H_lt_leftorright_eq.
              + exact (at_right C z).
              + exact IHH_lt_leftorright_eq.
              + exact IHH_lt_leftorright_eq.
          Defined.
          *)

          (** COMPARE [loc_rev] with [cat_term_arrow_on_nodes_target] above **)
          Fixpoint loc_rev (A : objects) (x : nodes A) {struct x} : nodes (object_at_node x) -> nodes A.
          Proof.
            destruct x.
            - exact (fun y_x => y_x).
            - exact (fun y_x => ( at_left (loc_rev A x y_x) B )).
            - exact (fun y_x => ( at_right A (loc_rev B x y_x) )).
          Defined.
          (* COMPARE [loc_rev] with [cat_term_arrow_on_nodes_target]
          Definition cat_term_arrow_on_nodes_target :
            forall A' B' (f' : arrows A' B') A B (f : arrows A B) (term_arrow_f'_f : term_arrow f' f)
            : nodes B' -> nodes B.

            induction term_arrow_f'_f as [ | A B f term_arrow_f'_f IH_term_arrow_f'_f A0 | A A0 B0 f term_arrow_f'_f IH_term_arrow_f'_f ].
            - exact (fun y => y).
            - exact (fun y => at_left (IH_term_arrow_f'_f y) A0).
            - exact (fun y => at_right A (IH_term_arrow_f'_f y)).
          Defined.
          *)
          (** (*TOO GENERAL*)
          Lemma lem323 (A : objects) (x : nodes A) (y : nodes (object_at_node x)) : lt_leftorright_eq x (loc_rev x y).
            induction x; simpl; auto.
          Defined.
          Hint Resolve lem323. *)
          Fixpoint loc_rev_right (A : objects) (x : nodes A) (y_x : nodes (object_at_node x)) (H_lt_right_x_x_y_x : lt_right (self (object_at_node x)) y_x) {struct x} : lt_right x (loc_rev x y_x).
          Proof.
          (* destruct x; simpl in *; auto.
          Defined. *)
          destruct x.
          - exact H_lt_right_x_x_y_x.
          - simpl in *; constructor; exact (loc_rev_right _ x y_x H_lt_right_x_x_y_x).
          - simpl in *; constructor; exact (loc_rev_right _ x y_x H_lt_right_x_x_y_x).
          Defined.
          Hint Resolve loc_rev_right.
          Fixpoint loc (A : objects) (x : nodes A) (y : nodes A) (H_lt_right_x_y : lt_right x y) {struct H_lt_right_x_y} : nodes (object_at_node x).
          Proof.
             destruct H_lt_right_x_y.
              + exact (at_right C z).
              + exact (loc B x y H_lt_right_x_y).
              + exact (loc B x y H_lt_right_x_y).
          Defined.
          Fixpoint loc' (A : objects) (x : nodes A) (y : nodes A) (H_lt_left_x_y : lt_left x y) {struct H_lt_left_x_y} : nodes (object_at_node x).
          Proof.
             destruct H_lt_left_x_y.
              + exact (at_left z C).
              + exact (loc' B x y H_lt_left_x_y).
              + exact (loc' B x y H_lt_left_x_y).
          Defined.
          Lemma loc_right (*lem325*) (A : objects) (x : nodes A) (y : nodes A) (H_lt_right_x_y : lt_right x y) : lt_right (self (object_at_node x)) (loc H_lt_right_x_y).
            induction H_lt_right_x_y; simpl; auto.
          Defined.
          Hint Resolve loc_right.
          Lemma loc'_left (A : objects) (x : nodes A) (y : nodes A) (H_lt_left_x_y : lt_left x y) : lt_left (self (object_at_node x)) (loc' H_lt_left_x_y).
            induction H_lt_left_x_y; simpl; auto.
          Defined.
          Hint Resolve loc'_left.
          Lemma loc'_left_once (A : objects) (x : nodes A) (y : nodes A) (H_lt_left_once_x_y : lt_left_once x y) (H_lt_left_x_y : lt_left x y) : lt_left_once (self (object_at_node x)) (loc' H_lt_left_x_y).
            induction H_lt_left_x_y; simpl; dependent destruction H_lt_left_once_x_y; auto.
          Defined.
          Hint Resolve loc'_left_once.
          Lemma lem543 (A : objects) (x : nodes A) (y : nodes A) (H_lt_right_x_y : lt_right x y):  loc_rev x (loc H_lt_right_x_y) = y.
            induction x; dependent destruction H_lt_right_x_y;
            [ simpl; reflexivity
            | simpl; rewrite IHx; reflexivity ..
            ].          
          Defined.
          Hint Resolve lem543.
          Lemma lem337 (A : objects) (x : nodes A) (y_x : nodes (object_at_node x))  (H_lt_right_x_x_y_x : lt_right (self (object_at_node x)) y_x) : loc (loc_rev_right x H_lt_right_x_x_y_x) = y_x.
            induction x.
            - simpl in *. (*Fail dependent inversion_clear H_lt_right_x_x_y_x.*) dependent destruction H_lt_right_x_x_y_x. simpl. reflexivity.
            - simpl in *. auto.
            - simpl in *. auto.
          Defined.
          Hint Resolve lem337.

          (**?? lack loc_rev_right <o loc_right = id , loc_right <o loc_rev_right = id ??**)
          (* direction useful later:  loc_rev <o loc = id *)
          Lemma lem231 (A : objects) (fx : nodes A) (fy'_loc : nodes (object_at_node fx)) (fw_loc : nodes (object_at_node fx)) (H_lt_right : lt_right fw_loc fy'_loc)
          : lt_right (loc_rev fx fw_loc) (loc_rev fx fy'_loc).

            induction fx; simpl; auto. (** :D 1 attempt only, I am too good for this :D **)
            Defined.
          Hint Resolve lem231.

          Lemma lem232 (A : objects) (fx : nodes A) (fy'_loc : nodes (object_at_node fx)) (fw_loc : nodes (object_at_node fx)) (H_lt_right_once : lt_right_once fw_loc fy'_loc)
          : lt_right_once (loc_rev fx fw_loc) (loc_rev fx fy'_loc).

            induction fx; simpl; auto. (** :D 1 attempt only, I am too good for this :D **)
            Defined.
          Hint Resolve lem232.
          
          (*E = object_at_node (f x)*)
          Definition list_from_lt_right_once_almost (*list_from_no_medium*) (E : objects) (fy'_loc : nodes E)
                   (H_lt_right : lt_right (self E) fy'_loc)
                   (H_no_medium_loc : (forall fw_loc : nodes E, lt_right fw_loc fy'_loc -> lt_right (self E) fw_loc -> Empty_set))
          : {E1 : objects & {E2 : objects & {H_eq_tensor : eq (up_0 E1 E2) E &
            {Dlist : list objects & 
            {H_same_foldright : objects_same (foldright (object_at_node fy'_loc) Dlist) E2 & 
             nodes_map (objects_same_eq H_eq_tensor) (at_right E1 (nodes_map H_same_foldright (foldrightn_self (object_at_node fy'_loc) Dlist))) = fy'_loc }}}}}%type.

            dependent destruction H_lt_right (*/!\ names C B *). 
            split with C; split with B; split with eq_refl.

            assert (H_no_medium_loc_loc : forall fw : nodes B, lt_right fw z -> Empty_set).
            { intros.
              assert (Htemp': lt_right (at_right C fw) (at_right C z)) by auto.
              eapply H_no_medium_loc with (1:=Htemp'); constructor.
            } 
            assert (H_lem009900 := @lem009900 B z H_no_medium_loc_loc).
            destruct H_lem009900 as (H_lem009900_Dlist & H_lem009900_H_same_foldright & H_lem009900_nodes_map).

            split with H_lem009900_Dlist; split with H_lem009900_H_same_foldright.
            simpl object_at_node; rewrite H_lem009900_nodes_map.
            autorewrite * with core using eauto.
            (*ALT:  replace (@objects_same_eq _ (C/\B) eq_refl) with (objects_same_refl (C/\B)) by auto; auto.*)
          Defined.
          Hint Resolve list_from_lt_right_once_almost.
          
          assert (H_E1_E2_list_E2_eq
                  : {E1 : objects & {E2 : objects & 
                    {H_eq_tensor : eq (up_0 E1 E2) (object_at_node (f x)) & 
                    {Dlist : list objects & 
                    {H_eq_foldright : objects_same (foldright (object_at_node (loc H_lt_right_fx_fy')) Dlist) E2 & 
                                                   nodes_map (objects_same_eq H_eq_tensor) (at_right E1 
                                                   (nodes_map H_eq_foldright (foldrightn_self (object_at_node (loc H_lt_right_fx_fy')) Dlist))) 
                                      = (loc H_lt_right_fx_fy') }}}}}%type).
          { (**/!\OLD GENERATE EVARS AND EXISTENTIALS GOALS WHICH ARE IMPOSSIBLE TO PROVE
            (*eauto*) (eapply list_from_lt_right_once_almost; eauto). **)
            assert (H_lt_right_fx_fy'_loc : lt_right (self (object_at_node (f x))) (loc H_lt_right_fx_fy') ) by (*auto*) (apply loc_right; auto). (*used as hypothesis for H_E1_E2_list_E2_eq below*)
            assert (H_lt_right_once_almost_fx_fy'_loc : (forall fw_loc : nodes (object_at_node (f x)), lt_right fw_loc (loc H_lt_right_fx_fy') -> lt_right (self (object_at_node (f x))) fw_loc -> Empty_set)).
            { intros fw_loc J1 J2. apply (H_lt_right_once_almost_fx_fy' (loc_rev (f x) fw_loc)).
              replace (f y') with (loc_rev (f x) (loc H_lt_right_fx_fy')) by auto. auto.
              Lemma lem220 A (x : nodes A) : loc_rev x (self (object_at_node x)) = x. induction x; simpl in *; auto. Defined. Hint Resolve lem220. Hint Rewrite lem220 using eauto.
              cut (lt_right (loc_rev (f x) (self (object_at_node (f x)))) (loc_rev (f x) fw_loc)); [
                  rewrite lem220; tauto
                | auto ].
            }
          eapply (list_from_lt_right_once_almost H_lt_right_fx_fy'_loc H_lt_right_once_almost_fx_fy'_loc).
          }
          
          destruct H_E1_E2_list_E2_eq as (E1 & E2 & H_object_at_node_fx & list_E2 & H_list_E2_objects & H_list_E2_nodes).
          assert (H_list_E2 := objects_eq_same H_list_E2_objects).

          (*next Lemma object_at_node loc = object_at_node id *)
          Lemma lem121 (A : objects) (x : nodes A) (y : nodes A) (H_lt_right_x_y : lt_right x y) : object_at_node (loc H_lt_right_x_y) = object_at_node y.

            induction H_lt_right_x_y; simpl; auto. (* :D 1 attempt only :) *)
            Defined.
          Hint Resolve lem121.
          Hint Rewrite lem121 using auto.

          replace (object_at_node (loc H_lt_right_fx_fy')) with (object_at_node (f y')) in H_list_E2 by auto.
          
          destruct list_E2 as [ | E2_3 list_E2_2].
          - (**unitt2 case **)
            subst E2. simpl in H_object_at_node_fx. 
            assert (H_lt_right_once_fx_fy' : lt_right_once (f x) (f y')).
            {
              Lemma lem123 (A E : objects) (x y : nodes A) (H_lt_right : lt_right x y) (Heq : object_at_node x = (E /\ object_at_node y)) : lt_right_once x y.
                induction H_lt_right.
                - simpl in *. dependent destruction Heq. assert (lengthl B = lengthl (object_at_node z)) by (f_equal; assumption). assert (z = self B) by auto (**apply lem005900*). subst z. constructor.
                - simpl in *; auto. (* :D 1 attempt only *)
                - simpl in *; auto.
              Defined.
              Hint Resolve lem123.
              Show.
              eauto.
            }
            assert (H_object_at_node_y : object_at_node y = object_at_node (f y)) by auto (* apply H_object_at_node; exact xyy'_prop_4)*).
            assert (H_object_at_node_y' : object_at_node y' = object_at_node (f y')) by auto (* apply H_object_at_node; exact xyy'_prop_4)*).

            assert (H_node_is_lettery_x : node_is_lettery f x) by eauto (*(eapply lem010800; eauto)*).
            assert (H_object_at_node_x : object_at_node x = object_at_node (f x)) by eauto (*eapply lem011000; eauto*).

            (*/1\FOCUS/!\*)
            set (more_cumul_letteries cumul_letteries H_cumul_letteries_wellform H_cumul_letteries_x_false) as H_more_cumul_letteries.
            set (projT1 H_more_cumul_letteries) as H_more_cumul_letteries_1.
            set (projT1(projT2 H_more_cumul_letteries)) as H_more_cumul_letteries_2.
            set (projT2(projT2 H_more_cumul_letteries)) as H_more_cumul_letteries_3.
            hnf in (type of H_more_cumul_letteries_3).
            fold H_more_cumul_letteries_2 in H_more_cumul_letteries_3.
            fold H_more_cumul_letteries_1 in H_more_cumul_letteries_2, H_more_cumul_letteries_3.

            (* assert (H_more_cumul_letteries := more_cumul_letteries cumul_letteries H_cumul_letteries_wellform H_cumul_letteries_x_false).
               destruct H_more_cumul_letteries as (H_more_cumul_letteries_1 & H_more_cumul_letteries_2 & H_more_cumul_letteries_3).
            *)

            assert (H_more_cumul_letteries_4 : lengthn'' H_more_cumul_letteries_1 H_more_cumul_letteries_2 <= S len) by auto with zarith (*/!\note that without those two [fold] above this alt proof only : ((*/!\careful with this non-clean proof/!\*) subst H_more_cumul_letteries_1; subst H_more_cumul_letteries_2; auto with zarith) *).

            assert (H_more_cumul_letteries_5_satur : forall y : nodes B, H_more_cumul_letteries_1 y = true -> forall z : nodes B, lt_leftorright_eq y z ->  H_more_cumul_letteries_1 z = true).
            {
              intros t. unfold H_more_cumul_letteries_1. unfold projT1. unfold H_more_cumul_letteries.
              unfold more_cumul_letteries.
              destruct (nodes_eq_dec t x) as [Heq_t_x | Heq_t_x].
              + subst t. intros _ t [H_lt_leftorright_eq_x_t | [H_lt_leftorright_eq_x_t | H_lt_leftorright_eq_x_t]].
              - subst t. SearchRewrite (nodes_eq_dec _ _) (*nothing*). 
                destruct (nodes_eq_dec x x) as [J1 | J1]; [reflexivity | exfalso; apply J1; reflexivity].
              - destruct (nodes_eq_dec t x) as [J1 | J1]; [elimtype Empty_set; apply (lem007100 J1); auto | idtac].
                SearchAbout (  lt_left_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010500*)
                assert (H_lt_leftorright_eq_y_t : lt_leftorright_eq y t) by ( apply (lem010500 H_lt_left_once_x_y H_lt_leftorright_eq_x_t)).
                assert (H_cumul_letteries_t_true : cumul_letteries t = true) by (eapply (H_cumul_letteries_satur _ H_cumul_letteries_y_true); eassumption).
                exact H_cumul_letteries_t_true.
              - destruct (nodes_eq_dec t x) as [J1 | J1]; [elimtype Empty_set; apply (lem007100 J1); auto | idtac].
                SearchAbout (  lt_right_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010600*)
                assert (H_lt_leftorright_eq_y'_t : lt_leftorright_eq y' t) by ( apply (lem010600 H_lt_right_once_x_y' H_lt_leftorright_eq_x_t)).
                assert (H_cumul_letteries_t_true : cumul_letteries t = true) by (eapply (H_cumul_letteries_satur _ H_cumul_letteries_y'_true); eassumption).
                exact H_cumul_letteries_t_true.
                + intros J1 z J2. destruct (nodes_eq_dec z x) as [J3 | J3]; [reflexivity | idtac].
                  apply (H_cumul_letteries_satur t); assumption.
            }


            assert (H_node_is_lettery_more: forall x : B,
                      H_more_cumul_letteries_1 x = true -> node_is_lettery f x).
            {
              intros t. unfold H_more_cumul_letteries_1. unfold projT1. unfold H_more_cumul_letteries.
              unfold more_cumul_letteries.
              destruct (nodes_eq_dec t x) as [Heq_t_x | Heq_t_x].
              + subst t. intros. exact H_node_is_lettery_x.
              + clear Heq_t_x.  revert t. exact H_node_is_lettery.
            }
            assert (H_object_at_node_more: forall x : B,
                      H_more_cumul_letteries_1 x = true ->  object_at_node x = object_at_node (f x)).
            {
              intros t. unfold H_more_cumul_letteries_1. unfold projT1. unfold H_more_cumul_letteries.
              unfold more_cumul_letteries.
              destruct (nodes_eq_dec t x) as [Heq_t_x | Heq_t_x].
              + subst t. intros. exact H_object_at_node_x.
              + clear Heq_t_x.  revert t. exact H_object_at_node.
            }
            
            assert (H_cumul_B_more := H_cumul_B).

            exact (IHlen H_more_cumul_letteries_1 H_more_cumul_letteries_2 H_more_cumul_letteries_5_satur H_more_cumul_letteries_4 A f H_node_is_lettery_more H_object_at_node_more H_cumul_B_more).
            Guarded.

          - (**nodal_multi_bracket case**)
            clear H_list_E2 (**was useful for unitt2 case only**).
              
            Fixpoint move_foldright (A : objects) (B_list : list objects) {struct B_list} : forall C : objects, {B : objects & {list_C : list objects & objects_same ((A /\ B) /\\ list_C) (A /\\ (C :: B_list)%list) }}.

            Proof.
              destruct B_list as [ | C0 B_list].
              - intros C. split with C. split with nil. simpl. constructor; exact (objects_same_refl _).
              - intros C. simpl. specialize move_foldright with (A:=A) (B_list:=B_list)(C:=C0).
                (* destruct move_foldright as (B & list_C0 & Heq_B_list_C0).*)
                split with (projT1 move_foldright). split with (C :: (projT1(projT2 move_foldright)))%list. simpl in *. constructor; [exact (projT2(projT2 move_foldright))(*Heq_B_list_C0*) | exact (objects_same_refl _)]. 
            Defined.

            Lemma lem080_test (A C0 C : objects) (B_list : list objects)
            : projT1 (move_foldright A (C0 :: B_list) C) = projT1 (move_foldright A B_list C0).
              simpl. reflexivity.
            Defined.

            
            (* Fixpoint move_foldright (A : objects) (B_list : list objects) {struct B_list} : forall C : objects, {B : objects & {list_C : list objects & (A /\\ (C :: B_list)%list) = ((A /\ B) /\\ list_C) }}.

            Proof.
              destruct B_list as [ | C0 B_list].
              - intros C. split with C. split with nil. simpl. reflexivity.
              - intros C. simpl. specialize move_foldright with (A:=A) (B_list:=B_list)(C:=C0).
                destruct move_foldright as (B & list_C0 & Heq_B_list_C0).
                split with B. split with (C :: list_C0)%list. simpl in *. rewrite Heq_B_list_C0. reflexivity.
            Defined.

            Check foldrightn_self.
            Fixpoint move_foldrightn_self (A : objects) (B_list : list objects) (C : objects) : let B_list_C_prop := (move_foldright A B_list C) in nodes_map (projT2 (projT2 B_list_C_prop)) (foldrightn_self (A /\ (projT1 B_list_C_prop))(projT1(projT2 B_list_C_prop))) = foldrightn_self A (C :: B_list).
            Proof.
              destruct B_list as [ | C0 B_list].
              - simpl. unfold solution_left. unfold eq_rect_r; unfold eq_rect. simpl. Fail reflexivity. Abort. 
            *)


            Fixpoint move_foldrightn_self (A : objects) (B_list : list objects) (C : objects) 
            : let B_list_C_prop := (move_foldright A B_list C) 
              in nodes_map (projT2 (projT2 B_list_C_prop)) 
                           (foldrightn (foldrightn_self A ((projT1 B_list_C_prop) :: nil)) (projT1(projT2 B_list_C_prop))) 
                 = foldrightn_self A (C :: B_list).

            Proof.
              destruct B_list as [ | C0 B_list].
              - lazy zeta. simpl nodes_map. compute -[nodes_map objects_same_refl].
                autorewrite * with core using reflexivity.
              - lazy zeta in *.
                simpl (projT1 (move_foldright A (C0 :: B_list) C)).
                simpl (projT1 (projT2 (move_foldright A (C0 :: B_list) C))).
                simpl (projT2 (projT2 (move_foldright A (C0 :: B_list) C))).
                simpl foldrightn.
                (**/!\why fail?  Fail progress autorewrite * with core using eauto.
                Fail erewrite lem099. *)
                simpl nodes_map at 1. compute -[nodes_map objects_same_refl move_foldright foldrightn_self foldrightn projT1 projT2].
                simpl foldrightn_self. replace ((at_left (foldrightn_self A B_list) C0)) with ((foldrightn_self A (C0 ::B_list))) by reflexivity.
                f_equal. apply move_foldrightn_self. 
            Defined.

            (**>>>>>>>>>>>>HERE<<<<<<<<<<<
            TWO-STEP TRANSFERT TO SOLVE THE MULTI_BRACKET FOLDING-STYLE? nodes_map along two horizontal objects_same
            IS TWO nodes_map along TWO vertical objects_same TOO HEAVY? DO EVERYTHING IN E2 ONLY ?
            **)

            (*rewrite H_eq_E2_2_list_E2_3 in H_object_at_node_fx.*)
            (*clear H_eq_E2_2_list_E2_3 E2_3 list_E2_2.*)

            assert ( H_object_at_node_fx_alt 
                     : object_at_node (f x) = 
                       up_0 E1  ( ( up_0 (object_at_node (loc H_lt_right_fx_fy'))
                                    (projT1 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3)) ) /\\
                                    (projT1 (projT2 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3))) ) ).

            {
              assert ( H_object_at_node_fx_alt' 
                       : up_0 E1 E2 =
                         up_0 E1  ( ( up_0 (object_at_node (loc H_lt_right_fx_fy'))
                                      (projT1 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3)) ) /\\
                                      (projT1 (projT2 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3))) ) ).
              {
                assert (eq (object_at_node (loc H_lt_right_fx_fy') /\\ E2_3 :: list_E2_2) E2) by auto.
                subst E2. f_equal. symmetry.
                exact (objects_eq_same (projT2 (projT2 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2  E2_3)))).
              } 
              rewrite <- H_object_at_node_fx_alt'.
              symmetry; assumption. 
            }

(* this is the old [ destruct (@nodal_multi_bracket_left _ ], see fuller nodal_multi_bracket_left_full below
Check @nodal_multi_bracket_left.
destruct (@nodal_multi_bracket_left A (f x) 
 E1 (object_at_node (loc H_lt_right_fx_fy'))  
(projT1 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3))
(projT1 (projT2 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3)))
H_object_at_node_fx_alt)
as (M & f' & H_term_arrow_f' & H_eq_f'x & H_cumul_lt_right_A).
*)

            rewrite <- move_foldrightn_self in H_list_E2_nodes.
            set (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3) as mfr in *.

(*assert (mfrT2T2 := projT2(projT2 mfr)).
lazy beta in mfrT2T2.*)
(* this was used for the old [destruct (@nodal_multi_bracket_left _ ] above
assert ( H_object_at_node_fx_alt_alt : objects_same
              (E1 /\ ((object_at_node (loc H_lt_right_fx_fy') /\ projT1 mfr) /\\
               projT1 (projT2 mfr)))
              (E1 /\ (object_at_node (loc H_lt_right_fx_fy') /\\ E2_3 :: list_E2_2)) ).
{ constructor.
  exact (objects_same_refl E1).
  exact (projT2(projT2 ( (*mfr*) move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3))).
}
*)
(* destruct (@nodal_multi_bracket_left A (f x) E1 (object_at_node (f y')) E2_2 list_E2_3 (eq_sym H_object_at_node_fx)) as (M & f' & H_term_arrow_f' & H_eq_f'x & H_cumul_lt_right_A). *)


            Lemma lem080 (A B C : objects) (Dlist : list objects) 
            : lt_right_once ( (multi_bracket_left A B C Dlist) (self _) )
                            ( (multi_bracket_left A B C Dlist) ( at_right A ( foldrightn (foldrightn_self B (C :: nil)) Dlist ) ) ).

              induction Dlist as [ | E Dlist].
              - compute. auto.
              - 
                Lemma lem081 (A B C E : objects) (Dlist : list objects)
                : (projT1 (multi_bracket_left_specif A B C (E :: Dlist))) 
                  = (((projT1 (multi_bracket_left_specif A B C Dlist)) /\1 unitt E) <o (bracket_left A (foldright (B /\ C) Dlist) E)).
                reflexivity.
                Defined.
                Hint Resolve lem081.
                Hint Rewrite lem081 using eauto.
                unfold multi_bracket_left (*autounfold*). autorewrite * with core using eauto (*rewrite lem081*).
                simpl arrows_assoc_on_nodes. unfold solution_left, block, eq_rect_r, eq_rect, eq_rec, eq_rec. simpl.
                constructor.
                fold (multi_bracket_left A B C Dlist).
                assumption.
            Defined.
            Hint Resolve lem080.

            Definition objects_same_trans A0 A1 (H_objects_same_1 : objects_same A0 A1) : forall A2 (H_objects_same_2: objects_same A1 A2),  objects_same A0 A2.

              induction H_objects_same_1.
              - intros. dependent destruction H_objects_same_2.
                constructor.
              - intros. dependent destruction H_objects_same_2.
                constructor.
                + apply IHH_objects_same_1_1. assumption.
                + apply IHH_objects_same_1_2. assumption.
            Defined.
            Hint Resolve objects_same_trans.
            Print Implicit objects_same_trans.
            Arguments objects_same_trans [A0] [A1] !H_objects_same_1 [A2] !H_objects_same_2.

            Definition objects_same_sym A0 A1 (H_objects_same : objects_same A0 A1) : objects_same A1 A0.

              induction H_objects_same.
              - constructor.
              - constructor; assumption.
            Defined.
            Hint Resolve objects_same_sym.

            Arguments solution_left / .
            Arguments block / .
            Arguments eq_rect_r / .
            Arguments eq_rect / .
            Arguments eq_rec_r / .
            Arguments eq_rec / .
            Arguments eq_ind_r / .
            Arguments eq_ind / .

            Lemma lem077 A0 A1 (H_objects_same_1 : objects_same A0 A1) 
            : forall A2 (H_objects_same_2: objects_same A1 A2) (x : nodes A0)
              , nodes_map H_objects_same_2 (nodes_map H_objects_same_1 x) = nodes_map (objects_same_trans H_objects_same_1 H_objects_same_2) x.
                        
              induction H_objects_same_1;
              dependent destruction H_objects_same_2;
              dependent destruction x;
              simpl;
              try reflexivity (*base step*);
              (*unfold solution_left, block, eq_rect_r, eq_rect, eq_rec_r, eq_rec, eq_ind_r, eq_ind; simpl (**finish simpl of nodes_map. the [ Arguments / ] commands preceding above solve this**); *)
              f_equal;
              (apply IHH_objects_same_1_1 ||
                     apply IHH_objects_same_1_2).
              
            Defined.
            Hint Resolve lem077.
            Hint Rewrite lem077 using eauto.
            
            (**see lem100 above . lem078 is particular of lem100 above **)
            Lemma lem078 A B0 (x : nodes B0) B1 (H_objects_same : objects_same B0 B1)
            : at_right A (nodes_map H_objects_same x) = nodes_map (objects_same_cons2 (objects_same_refl A) H_objects_same) (at_right A x).

              reflexivity.
            Defined.
            Hint Resolve lem078.
            Hint Rewrite lem078 using eauto.

            rewrite lem077 in H_list_E2_nodes.
            rewrite lem078 in H_list_E2_nodes.
            rewrite lem077 in H_list_E2_nodes.

            (*better formatting below
assert ( H_list_E2_nodes_self : nodes_map
                      (objects_same_trans
                         (objects_same_cons2 (objects_same_refl E1)
                            (objects_same_trans (projT2 (projT2 mfr))
                               H_list_E2_objects))
                         (objects_same_eq H_object_at_node_fx))
                      (self _) =
                                self _ ). *)

            assert ( H_list_E2_nodes_self :
                       nodes_map
                         (objects_same_trans
                            (objects_same_cons2 (objects_same_refl E1)
                                                (objects_same_trans (projT2 (projT2 mfr)) H_list_E2_objects))
                            (objects_same_eq H_object_at_node_fx))
                         (self _ (*
        (E1 /\
         (object_at_node (loc H_lt_right_fx_fy') /\ projT1 mfr) /\\
         projT1 (projT2 mfr))*)) 
                       = self _ (*(object_at_node (f x))*) ).
            {
              (*rewrite <- ?lem077.
              rewrite -> ?lem098. *)

              Lemma lem079 A B (H_objects_same : objects_same A B) 
              : nodes_map H_objects_same (self _) = (self _).
                
                destruct H_objects_same; reflexivity (*also same as lem098*).
              Defined.
              Hint Resolve lem079.

              Show.
              apply lem079 (*auto*).
            }

            (*(lem070 (multi_bracket _ _ _ list_) (H_objects_same_amalgam) ) is the arrow lacked locally.
  ?..now what about putting some term_arrow onto this local arrow..? *)
            Lemma lem070 A0 E (f : arrows A0 E) A1 (H_objects_same : objects_same A0 A1)
            : arrows A1 E.

              Lemma lem071 A0 A1 (H_objects_same : objects_same A0 A1)
              : arrows A1 A0.
                
                induction H_objects_same.
                - exact (unitt _).
                - exact (IHH_objects_same1 /\1 IHH_objects_same2).
              Defined.
              Hint Resolve lem071.

              Show.
              refine (f <o _).
              auto (*apply lem071; assumption*). Show Proof.
            Defined.
            Hint Resolve lem070.
            Hint Unfold lem070.

            Lemma lem072 A0 A1 (H_objects_same : objects_same A0 A1)
            : forall x : nodes A1, (lem071 H_objects_same) x = nodes_map (objects_same_sym H_objects_same) x.

              induction H_objects_same.
              - reflexivity.
              - dependent destruction x.
                + reflexivity.
                + simpl. f_equal. apply IHH_objects_same1.
                + simpl. f_equal. apply IHH_objects_same2.
            Defined.
            Hint Resolve lem072.

            Lemma lem073 A0 E (f : arrows A0 E) A1 (H_objects_same : objects_same A0 A1) (x : nodes A1)
            : (lem070 f H_objects_same) x = f (nodes_map (objects_same_sym H_objects_same) x).

              autounfold. simpl.
              f_equal.
              auto (*apply lem072 *).
            Defined. 
            Hint Resolve lem073.

            (* assert (H_lt_right_once_f'fx_f'fy'_loc :
          lt_right_once (f' (f x)) (f' (f y')) )

 -| lt_right_once (H_term_arrow_f' ((lem070 mtb H_objects_same_amalg) (self (object_at_node (f x))))) (H_term_arrow_f' ((lem070 mtb H_objects_same_amalg) (loc H_lt_right_fx_fy')))

 -| lt_right_once ( ((lem070 mtb H_objects_same_amalg) (self (object_at_node (f x))))) ( ((lem070 mtb H_objects_same_amalg) (loc H_lt_right_fx_fy'))) by  cat_term_arrow_on_nodes_target H_term_arrow y = loc_rev (cat (self B')) y and lem232

 -| lt_right_once ((mtb (self (_ /\ (_ /\ _) /\\ _)))) ((mtb (at_right _ (foldrightn (foldrightn_self _ _) _))))

 |--| lem080 
             *)

            Lemma objects_same_term_arrow  A' B' (f' : arrows A' B') A B (f : arrows A B)(H_term_arrow_f'_f : term_arrow f' f)
            : objects_same B' (object_at_node (H_term_arrow_f'_f (self B'))).

              (*ALT: induction H_term_arrow_f'_f; simpl in *; auto.*)
              induction H_term_arrow_f'_f.
              - simpl. exact (objects_same_refl B').
              - simpl. exact (IHH_term_arrow_f'_f).
              - simpl. exact (IHH_term_arrow_f'_f).
            Defined.
            Hint Resolve objects_same_term_arrow.

            (**able to also use lem060 below to rewrite cat_term_arrow_on_nodes_target into loc_rev then use lemmma lem121 [object_at_node loc = object_at_node id]  *)

            Lemma objects_same_term_arrow_post1  A' B' (f' : arrows A' B') A B (f : arrows A B)(H_term_arrow_f'_f : term_arrow f' f) (x : nodes B')
            : objects_same (object_at_node x) (object_at_node (H_term_arrow_f'_f x)).

              (*ALT induction H_term_arrow_f'_f; simpl in *; auto.*)
              induction H_term_arrow_f'_f.
              - simpl. exact (objects_same_refl _).
              - simpl. exact (IHH_term_arrow_f'_f).
              - simpl. exact (IHH_term_arrow_f'_f).
            Defined.
            Hint Resolve objects_same_term_arrow_post1.
            
            Lemma lem060  A' B' (f' : arrows A' B') A B (f : arrows A B)(H_term_arrow_f'_f : term_arrow f' f) (x : nodes B')
            : cat_term_arrow_on_nodes_target H_term_arrow_f'_f x = loc_rev (cat_term_arrow_on_nodes_target H_term_arrow_f'_f (self B')) (nodes_map (objects_same_term_arrow H_term_arrow_f'_f) x).

              induction H_term_arrow_f'_f.
              - simpl. autorewrite * with core using reflexivity.
              - simpl. f_equal. apply IHH_term_arrow_f'_f.
              - simpl. f_equal. apply IHH_term_arrow_f'_f.
            Defined.
            Hint Resolve lem060.
            Hint Rewrite lem060 using eauto.
                    
            Lemma lem044 A B C : ( forall x y : nodes ((A /\ B) /\ C), ( (lt_left_eq (self _) ((rev (bracket_left A B C)) y)) -> Empty_set ) -> lt_left x y -> lt_left ((rev (bracket_left A B C)) x) ((rev (bracket_left A B C)) y) ).
                      
              simpl; intros x y H_x_is_self H_lt_left_x_y.
              dependent destruction H_lt_left_x_y.
              + dependent destruction z.
              - elimtype Empty_set. simpl in *. auto.
              - simpl in *. elimtype Empty_set. auto.
              - simpl in *. auto.
                + dependent destruction x0; dependent destruction y0; dependent destruction H_lt_left_x_y.
                  simpl. constructor.
                  simpl. constructor. assumption.
                  simpl. constructor. constructor. assumption.
                + simpl. constructor. constructor. assumption.
            Defined.
            Hint Resolve lem044.

            Lemma lem043 A B C Dlist : ( forall x y : nodes (((A /\ B) /\ C) /\\ Dlist), ( (lt_left_eq (self _) ((rev (multi_bracket_left A B C Dlist)) y))  -> Empty_set ) -> lt_left x y -> lt_left ((rev (multi_bracket_left A B C Dlist)) x) ((rev (multi_bracket_left A B C Dlist)) y) ).

              induction Dlist as [ | D0 Dlist].
              - (**ALT: apply lem044. **) simpl foldright; simpl multi_bracket_left; auto. 
              - simpl multi_bracket_left. 
                Arguments arrows_assoc_on_nodes : simpl nomatch. (**/!\**)
                Arguments rev : simpl nomatch. (**/!\**)
                Arguments bracket_right_on_nodes : simpl nomatch. (**/!\**)
                simpl.
                intros  x y H_x_is_self H_lt_left.
                dependent destruction x; dependent destruction y;
                dependent destruction H_lt_left.
                + simpl arrows_assoc_on_nodes.
                  replace (bracket_right_on_nodes (self ((A /\ (B /\ C) /\\ Dlist) /\ D0))) with ( (rev (bracket_left A ((B /\ C) /\\ Dlist) D0)) (self ((A /\ (B /\ C) /\\ Dlist) /\ D0)) ) by reflexivity. 
                  replace (bracket_right_on_nodes (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) y) D0)) with ((rev (bracket_left A ((B /\ C) /\\ Dlist) D0)) (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) y) D0)) by reflexivity.
                  apply lem044.
                  * exact H_x_is_self.
                  * constructor.
                + simpl.
                  replace (bracket_right_on_nodes (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) x) D0)) with ((rev (bracket_left A ((B /\ C) /\\ Dlist) D0)) (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) x) D0)) by reflexivity.
                  replace (bracket_right_on_nodes (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) y) D0)) with ((rev (bracket_left A ((B /\ C) /\\ Dlist) D0)) (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) y) D0)) by reflexivity.
                  apply lem044.
                  * exact H_x_is_self.
                  * constructor. apply IHDlist. 2: exact H_lt_left.
                    simpl in *.
                    intros [J1 | J1].
                    { apply H_x_is_self.
                      rewrite <- J1. simpl. left. reflexivity. }
                    { apply H_x_is_self.
                      revert J1.
                      generalize (((rev (projT1 (multi_bracket_left_specif A B C Dlist))) y)) as t.
                      intros t J1. dependent destruction J1.
                      simpl. right. constructor. }
                + simpl in *. unfold unitt_on_nodes.
                  constructor. constructor. exact H_lt_left.
            Defined.
            Hint Resolve lem043.

            (**cats moved here from below **)
            
            Definition cat_term_arrow_on_nodes_source :
              forall A' B' (f' : arrows A' B') A B (f : arrows A B),
                term_arrow f' f -> A' -> A.

              intros ? ? ? ? ? ? term_arrow_f'_f.
              induction term_arrow_f'_f as [ | A B f term_arrow_f'_f IH_term_arrow_f'_f A0 | A A0 B0 f term_arrow_f'_f IH_term_arrow_f'_f ].
              - exact (fun y => y).
              - exact (fun y => at_left (IH_term_arrow_f'_f y) A0).
              - exact (fun y => at_right A (IH_term_arrow_f'_f y)).
            Defined.

            (**/!\ Ambiguous paths Coercion cat_term_arrow_on_nodes_source : term_arrow >-> Funclass. **)
            Notation cats := cat_term_arrow_on_nodes_source.

            Lemma objects_same_term_arrow_source  A' B' (f' : arrows A' B') A B (f : arrows A B)(H_term_arrow_f'_f : term_arrow f' f)
            : objects_same A' (object_at_node (cats H_term_arrow_f'_f (self A'))).

              (*ALT: induction H_term_arrow_f'_f; simpl in *; auto.*)
              induction H_term_arrow_f'_f.
              - simpl. exact (objects_same_refl A').
              - simpl. exact (IHH_term_arrow_f'_f).
              - simpl. exact (IHH_term_arrow_f'_f).
            Defined.
            Hint Resolve objects_same_term_arrow_source.

            Lemma lem059  A' B' (f' : arrows A' B') A B (f : arrows A B)(H_term_arrow_f'_f : term_arrow f' f) (x : nodes A')
            : cat_term_arrow_on_nodes_source H_term_arrow_f'_f x = loc_rev (cat_term_arrow_on_nodes_source H_term_arrow_f'_f (self A')) (nodes_map (objects_same_term_arrow_source H_term_arrow_f'_f) x).

              induction H_term_arrow_f'_f.
              - simpl. autorewrite * with core using reflexivity.
              - simpl. f_equal. apply IHH_term_arrow_f'_f.
              - simpl. f_equal. apply IHH_term_arrow_f'_f.
            Defined.
            Hint Resolve lem059.
            Hint Rewrite lem059 using eauto.

            Definition nodal_multi_bracket_left_full {A : objects} {x : nodes A} {A2 B2 C2 Dlist2} (H_same_object_at_node: objects_same (up_0 A2 ((B2 /\ C2) /\\ Dlist2)) (object_at_node x) )
            : { M : objects & { f' : arrows A M &
              { H_term_arrow_f_f' : (term_arrow (lem070 (multi_bracket_left A2 B2 C2 Dlist2) H_same_object_at_node) f') &
                prod ( (f' x) = H_term_arrow_f_f' ((lem070 (multi_bracket_left A2 B2 C2 Dlist2) H_same_object_at_node) (self (object_at_node x))) )
               (prod ( forall (z : nodes A) (H_lt_right_x_z : lt_right x z), (f' z) = H_term_arrow_f_f' ((lem070 (multi_bracket_left A2 B2 C2 Dlist2) H_same_object_at_node) (loc H_lt_right_x_z)) )
               (prod ( forall (z : nodes A) (H_lt_left_x_z : lt_left x z), (f' z) = H_term_arrow_f_f' ((lem070 (multi_bracket_left A2 B2 C2 Dlist2) H_same_object_at_node) (loc' H_lt_left_x_z)) )
               (prod ( forall n l : nodes A, ( n = x -> Empty_set) -> lt_right n l -> lt_right (f' n) (f' l) )
               (prod ( forall n l : nodes M, ( lt_left_eq x ((rev f') l) -> Empty_set ) -> lt_left n l -> lt_left ((rev f') n) ((rev f') l) )
               (prod ( forall n : nodes A, lt_par_or n x -> node_is_lettery f' n )
              (prod ( forall n : nodes A, lt_par_or n x -> object_at_node n = object_at_node (f' n) )
              ( cats H_term_arrow_f_f' (self (object_at_node x)) = x ) ) ) ) ) ) ) } } }.

              induction x as [ A | A x IHx B | A B x IHx ].
              - simpl in H_same_object_at_node.
                split with (((A2 /\ B2) /\ C2) /\\ Dlist2).
                split with (lem070 (multi_bracket_left A2 B2 C2 Dlist2) H_same_object_at_node).
                split with (term_arrow_self _).
                split.
                + reflexivity.
                + split.
                  * intros. dependent destruction H_lt_right_x_z. simpl loc.
                    simpl cat_term_arrow_on_nodes_target. simpl. reflexivity.
                  * { split.        
                      * intros. dependent destruction H_lt_left_x_z. simpl loc'.
                        simpl cat_term_arrow_on_nodes_target. simpl. reflexivity.
                      * split. 
                      - 
                        Lemma lem071' A0 A1 (H_objects_same : objects_same A0 A1) (n l : nodes A1) (H_lt_right_n_l : lt_right n l)
                        : lt_right ((lem071 H_objects_same) n) ((lem071 H_objects_same) l).

                        induction H_objects_same.
                      - simpl.
                        Hint Unfold unitt_on_nodes.
                        Hint Unfold bracket_left_on_nodes.
                        Hint Unfold bracket_right_on_nodes.
                        Hint Unfold arrows_assoc_on_nodes.
                        unfold unitt_on_nodes (*autounfold*). assumption.
                      - simpl (lem071 (objects_same_cons2 H_objects_same1 H_objects_same2)).
                        (**manual simpl is required here because cannot force node Arguments arrows_assoc_on_nodes !f !x in constructor form for all the cases of the arrow f (for example: unitt_on_nodes do not lack constructor form for the node x **)
                        generalize dependent (lem071 H_objects_same1);
                          generalize dependent (lem071 H_objects_same2); intros.
                        dependent destruction n; dependent destruction l;
                        dependent destruction H_lt_right_n_l;
                        simpl; auto.
                        Defined.
                        Hint Resolve lem071'.

                        Lemma lem071_post2 A0 A1 (H_objects_same : objects_same A0 A1)
                        : (lem071 H_objects_same) (self _) = (self _).
                          induction H_objects_same; simpl; reflexivity.
                        Defined.
                        Hint Resolve lem071_post2.
                        Hint Rewrite lem071_post2 using eauto.

                        Lemma lem071_post3 A0 A1 (H_objects_same : objects_same A0 A1) (x : nodes A1) (H_not_x_self : x = self _ -> Empty_set)
                        : (lem071 H_objects_same) x = (self _) -> Empty_set.
                          intros H_catx_self ; apply H_not_x_self.
                          induction H_objects_same; try exact H_catx_self; dependent destruction x; simpl in *; try reflexivity; dependent destruction H_catx_self.
                        Defined.
                        Hint Resolve lem071_post3.

                        intros. 
                        simpl; fold (multi_bracket_left A2 B2 C2 Dlist2).
                        cut ( lt_right ((lem071 H_same_object_at_node) n) ((lem071 H_same_object_at_node) l) ); 
                          [  cut ( ((lem071 H_same_object_at_node) n) = self _ -> Empty_set  );
                            [ intros; auto
                            | apply lem071_post3 (*/!\ name lem071_post3 *); assumption
                            ]
                           | auto].
                      - split.
                        + assert (H_same_object_at_node_eq := objects_eq_same H_same_object_at_node). subst A.
                          Lemma lem040 A (H_objects_same : objects_same A A) : H_objects_same = objects_same_refl A.
                            dependent induction H_objects_same.
                            simpl. reflexivity.
                            simpl. subst. reflexivity.
                          Defined. Hint Resolve lem040.
                          Show.
                          rewrite (lem040 H_same_object_at_node).

                          (**it is lemma lem036 below which is lacking, not lem038**)
                          Lemma lem038 A0 A1 (f : arrows A0 A1) (x : nodes A0) : (lem070 f (objects_same_refl A0)) x = f x.
                            autorewrite * with core using reflexivity. Check lem073.
                            rewrite lem073. f_equal. autorewrite * with core using reflexivity.
                            SearchPattern (nodes_map _ ?x = ?x). (**return lem212**)
                            Lemma lem037 A : objects_same_sym (objects_same_refl A) =  (objects_same_refl A).
                              induction A.
                              reflexivity.
                              simpl. rewrite IHA1. rewrite IHA2. reflexivity.
                            Defined. Hint Resolve lem037. Hint Rewrite lem037 using eauto.
                            Show.
                            rewrite lem037.
                            apply lem212.
                          Defined. Hint Resolve lem038. Hint Rewrite lem038 using eauto.

                          Lemma lem036 A0 A1 (f : arrows A0 A1) (x : nodes A1) : (rev (lem070 f (objects_same_refl A0))) x = (rev f) x.
                            simpl. generalize ((rev f) x).
                            intros z.
                            Lemma lem035 A x : (rev (lem071 (objects_same_refl A))) x = x.
                              induction A.
                              simpl.  unfold unitt_on_nodes. reflexivity.
                              simpl. dependent destruction x.
                              - simpl. reflexivity.
                              - simpl. f_equal. auto.
                              - simpl. f_equal. auto.
                            Defined. Hint Resolve lem035. Hint Rewrite lem035 using eauto.
                            Show. auto.
                          Defined. Hint Resolve lem036. Hint Rewrite lem036 using eauto.
                          Show.
                          intros n l .
                          rewrite ?lem036.
                          apply lem043.
                        + { split.
                            - intros n [H_lt_par_or_n_x | H_lt_par_or_n_x]; dependent destruction H_lt_par_or_n_x.
                            - split. 
                              + intros n [H_lt_par_or_n_x | H_lt_par_or_n_x]; dependent destruction H_lt_par_or_n_x.
                              + simpl. reflexivity.
                          }
                    }
              - { destruct (IHx H_same_object_at_node) as (IHx_M & IHx_f' & IHx_prop).
                  split with (IHx_M /\ B);
                    split with (IHx_f' /\1 unitt B).
                  destruct IHx_prop as (IHx_term_arrow & IHx_cat_term_arrow & IHx_cat_term_arrow_lt_right & IHx_cat_term_arrow_lt_left & IHx_nonvariance & IHx_nonvariance_2 & IHx_par_node_is_lettery & IHx_par_object_at_node & IHx_cats_self).
                  split with (term_arrow_at_left IHx_term_arrow _).
                  split.
                  + simpl arrows_assoc_on_nodes at 1.
                    rewrite IHx_cat_term_arrow. simpl cat_term_arrow_on_nodes_target. reflexivity.
                  + { split.
                      - intros. dependent destruction H_lt_right_x_z. simpl loc.
                        simpl arrows_assoc_on_nodes at 1.
                        rewrite (IHx_cat_term_arrow_lt_right _ H_lt_right_x_z).
                        simpl cat_term_arrow_on_nodes_target. reflexivity. 
                      - split.
                        * intros. dependent destruction H_lt_left_x_z. simpl loc'.
                          simpl arrows_assoc_on_nodes at 1.
                          rewrite (IHx_cat_term_arrow_lt_left _ H_lt_left_x_z).
                          simpl cat_term_arrow_on_nodes_target. reflexivity. 
                        * split. 
                        + intros n l H_not_n_x H_lt_right_n_l.
                          dependent destruction n; dependent destruction l;
                          dependent destruction H_lt_right_n_l; simpl;
                          solve 
                            [ try constructor; assumption
                            | constructor; apply IHx_nonvariance; 
                              [ intros; apply H_not_n_x; f_equal; assumption 
                              | assumption ] ].
                        +  { split.
                             - intros n l H_not_l_x.
                               dependent destruction n; dependent destruction l; simpl;
                               intros H_lt_left_n_l; dependent destruction H_lt_left_n_l; simpl; [
                                 constructor
                               | constructor; apply IHx_nonvariance_2; [ intros J1;  apply H_not_l_x; simpl rev; simpl; destruct J1 as [J1 | J1]; auto | assumption ]
                               | constructor; exact H_lt_left_n_l ].
                             - split.
                               + intros n [H_lt_par_or_n_x | H_lt_par_or_n_x ]; dependent destruction n; dependent destruction H_lt_par_or_n_x.
                                 * simpl. split. 
                                   { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. auto. - simpl. cut ( lt_leftorright_eq ( (IHx_f' n) ) ( (IHx_f' z) ) ) ; [ auto | ]. apply IHx_par_node_is_lettery; auto. - simpl. cut ( lt_leftorright_eq ( (IHx_f' n) ) ( (IHx_f' z) ) ) ; [ auto | ]. apply IHx_par_node_is_lettery; auto. }
                                   { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. replace (IHx_f' z). auto. - simpl. cut ( lt_leftorright_eq ( ((rev IHx_f') (IHx_f' n)) ) ( ((rev IHx_f') (IHx_f' z)) ) ); [auto | ]. apply IHx_par_node_is_lettery; auto.   - simpl. cut ( lt_leftorright_eq ( ((rev IHx_f') (IHx_f' n)) ) ( ((rev IHx_f') (IHx_f' z)) ) ); [auto | ]. apply IHx_par_node_is_lettery; auto. }
                                 * (*copy-paste of preceding case abode *) 
                                   simpl. split.
                                   { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. auto. - simpl. cut ( lt_leftorright_eq ( (IHx_f' n) ) ( (IHx_f' z) ) ) ; [ auto | ]. apply IHx_par_node_is_lettery; auto. - simpl. cut ( lt_leftorright_eq ( (IHx_f' n) ) ( (IHx_f' z) ) ) ; [ auto | ]. apply IHx_par_node_is_lettery; auto. }
                                   { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. replace (IHx_f' z). auto. - simpl. cut ( lt_leftorright_eq ( ((rev IHx_f') (IHx_f' n)) ) ( ((rev IHx_f') (IHx_f' z)) ) ); [auto | ]. apply IHx_par_node_is_lettery; auto.   - simpl. cut ( lt_leftorright_eq ( ((rev IHx_f') (IHx_f' n)) ) ( ((rev IHx_f') (IHx_f' z)) ) ); [auto | ]. apply IHx_par_node_is_lettery; auto. }
                                 * simpl. split. 
                                   { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. auto. - simpl; unfold unitt_on_nodes. auto. - simpl; unfold unitt_on_nodes. auto. }
                                   { (**copy-paste of case above**) intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. auto. - simpl; unfold unitt_on_nodes. auto. - simpl; unfold unitt_on_nodes. auto. }
                               + { split.
                                   - intros n [H_lt_par_or_n_x | H_lt_par_or_n_x ]; dependent destruction n; dependent destruction H_lt_par_or_n_x.
                                     * simpl. apply IHx_par_object_at_node; auto. 
                                     * simpl. apply IHx_par_object_at_node; auto. 
                                     * simpl. unfold unitt_on_nodes. reflexivity.
                                   - simpl.  f_equal. exact IHx_cats_self.
                                 }
                           } 
                    }
                }

              - { destruct (IHx H_same_object_at_node) as (IHx_M & IHx_f' & IHx_prop).
                  split with (A /\ IHx_M);
                    split with (unitt A /\1 IHx_f').
                  destruct IHx_prop as (IHx_term_arrow & IHx_cat_term_arrow & IHx_cat_term_arrow_lt_right & IHx_cat_term_arrow_lt_left & IHx_nonvariance & IHx_nonvariance_2 & IHx_par_node_is_lettery & IHx_par_object_at_node & IHx_cats_self).
                  split with (term_arrow_at_right _ IHx_term_arrow).
                  (**from here until below, copy-paste same as the induction case [at_right] above **)
                  split.
                  + simpl arrows_assoc_on_nodes at 1.
                    rewrite IHx_cat_term_arrow. simpl cat_term_arrow_on_nodes_target. reflexivity.
                  + { split.
                      - intros. dependent destruction H_lt_right_x_z. simpl loc.
                        simpl arrows_assoc_on_nodes at 1.
                        rewrite (IHx_cat_term_arrow_lt_right _ H_lt_right_x_z).
                        simpl cat_term_arrow_on_nodes_target. reflexivity.
                      - split.
                        * intros. dependent destruction H_lt_left_x_z. simpl loc.
                          simpl arrows_assoc_on_nodes at 1.
                          rewrite (IHx_cat_term_arrow_lt_left _ H_lt_left_x_z).
                          simpl cat_term_arrow_on_nodes_target. reflexivity. 
                        * split.
                        + intros n l H_not_n_x H_lt_right_n_l.
                          dependent destruction n; dependent destruction l;
                          dependent destruction H_lt_right_n_l; simpl;
                          solve 
                            [ try constructor; assumption
                            | constructor; apply IHx_nonvariance; 
                              [ intros; apply H_not_n_x; f_equal; assumption 
                              | assumption ] ].
                        + { split.
                            - intros n l H_not_l_x.
                              dependent destruction n; dependent destruction l; simpl;
                              intros H_lt_left_n_l; dependent destruction H_lt_left_n_l; simpl; [
                                constructor
                              | constructor; exact H_lt_left_n_l
                              | constructor; apply IHx_nonvariance_2; [ intros J1;  apply H_not_l_x; simpl rev; simpl; destruct J1 as [J1 | J1]; auto | assumption ] ].
                            - split.
                              + intros n [H_lt_par_or_n_x | H_lt_par_or_n_x ]; dependent destruction n; dependent destruction H_lt_par_or_n_x.
                                * simpl. split. 
                                  { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. auto. - simpl; unfold unitt_on_nodes. auto. - simpl; unfold unitt_on_nodes. auto. }
                                  { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. replace (unitt_on_nodes z). auto. - simpl; unfold unitt_on_nodes in J1 |- *; auto.  - simpl; unfold unitt_on_nodes in J1 |- *; auto. }
                                * (* _ _ _ *) 
                                  simpl. split.
                                  { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. auto. - simpl. cut ( lt_leftorright_eq ( (IHx_f' n) ) ( (IHx_f' z) ) ) ; [ auto | ]. apply IHx_par_node_is_lettery; auto. - simpl. cut ( lt_leftorright_eq ( (IHx_f' n) ) ( (IHx_f' z) ) ) ; [ auto | ]. apply IHx_par_node_is_lettery; auto. }
                                  { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. replace (IHx_f' z). auto. - simpl. cut ( lt_leftorright_eq ( ((rev IHx_f') (IHx_f' n)) ) ( ((rev IHx_f') (IHx_f' z)) ) ); [auto | ]. apply IHx_par_node_is_lettery; auto.   - simpl. cut ( lt_leftorright_eq ( ((rev IHx_f') (IHx_f' n)) ) ( ((rev IHx_f') (IHx_f' z)) ) ); [auto | ]. apply IHx_par_node_is_lettery; auto. }
                                * simpl. split. 
                                  { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. auto. - simpl. cut ( lt_leftorright_eq ( (IHx_f' n) ) ( (IHx_f' z) ) ) ; [ auto | ]. apply IHx_par_node_is_lettery; auto. - simpl. cut ( lt_leftorright_eq ( (IHx_f' n) ) ( (IHx_f' z) ) ) ; [ auto | ]. apply IHx_par_node_is_lettery; auto. }
                                  { intros z [J1 | [J1 | J1]]; dependent destruction z; dependent destruction J1. - simpl. replace (IHx_f' z). auto. - simpl. cut ( lt_leftorright_eq ( ((rev IHx_f') (IHx_f' n)) ) ( ((rev IHx_f') (IHx_f' z)) ) ); [auto | ]. apply IHx_par_node_is_lettery; auto.   - simpl. cut ( lt_leftorright_eq ( ((rev IHx_f') (IHx_f' n)) ) ( ((rev IHx_f') (IHx_f' z)) ) ); [auto | ]. apply IHx_par_node_is_lettery; auto. }
                              + { split. 
                                  - intros n [H_lt_par_or_n_x | H_lt_par_or_n_x ]; dependent destruction n; dependent destruction H_lt_par_or_n_x.
                                    * simpl. unfold unitt_on_nodes. reflexivity.
                                    * simpl. apply IHx_par_object_at_node; auto. 
                                    * simpl. apply IHx_par_object_at_node; auto. 
                                  - simpl.  f_equal. exact IHx_cats_self.
                                }
                          } 
                    }
                }
            Defined.

            set      (objects_same_trans
                        (objects_same_cons2 (objects_same_refl E1)
                                            (objects_same_trans (projT2 (projT2 mfr)) H_list_E2_objects))
                        (objects_same_eq H_object_at_node_fx)) as H_same_object_at_node in *.

            assert (H_lt_right_once_fx_fy'_loc: lt_right_once ( (lem070 (multi_bracket_left E1 (object_at_node (loc H_lt_right_fx_fy')) (projT1 mfr) (projT1 (projT2 mfr))) H_same_object_at_node) (self (object_at_node (f x))) )
 ( (lem070 (multi_bracket_left E1 (object_at_node (loc H_lt_right_fx_fy')) (projT1 mfr) (projT1 (projT2 mfr))) H_same_object_at_node) (loc H_lt_right_fx_fy') ) ).
            {
              (**this is the useful angle **)
              Lemma lem061 A A' (H_objects_same : objects_same A A') : forall (x : nodes A) (x' : nodes A') (Heq_nodes_map_x_x' : nodes_map H_objects_same x = x') , nodes_map (objects_same_sym H_objects_same) x' = x.
                
                induction H_objects_same.
                - intros. subst x'. simpl. unfold nodes_map (**/!\ in retro, above [Arguments nodes_map [A B] !H_objects_same !_.] is not such good idea because first case of H_objects_same do not lack node argument in constructor form **). reflexivity.
                -  intros. subst x'. simpl. dependent destruction x; simpl; eauto.
              Defined.
              Hint Resolve lem061.
              Hint Rewrite lem061 using eauto.

              (**ok, lem062 c'est pour la rester en forme seulement **)
              Lemma lem062 A A' (H_objects_same : objects_same A A') : forall (x : nodes A) (x' : nodes A') (Heq_nodes_map_x_x' : nodes_map (objects_same_sym H_objects_same) x' = x) , nodes_map H_objects_same x = x'.

                induction H_objects_same.
                - intros. subst x. simpl. unfold nodes_map (**/!\ in retro, above [Arguments nodes_map [A B] !H_objects_same !_.] is not such good idea because first case of H_objects_same do not lack node argument in constructor form **). reflexivity.
                -  intros. subst x. simpl. dependent destruction x'; simpl; eauto.
              Defined.
              Hint Resolve lem062.
              Hint Rewrite lem062 using eauto.

              simpl arrows_assoc_on_nodes; fold (multi_bracket_left E1 (object_at_node (loc H_lt_right_fx_fy')) (projT1 mfr) (projT1 (projT2 mfr))) (**/!\ this [fold] is not progressing ..**).
              rewrite 2lem072 (**/!\ shady syntax for two rewrite .. **).
              erewrite 2lem061 by eassumption.
              fold (multi_bracket_left E1 (object_at_node (loc H_lt_right_fx_fy')) (projT1 mfr) (projT1 (projT2 mfr))).
              apply lem080.
            }

            destruct (@nodal_multi_bracket_left_full A (f x) 
                                                     E1 (object_at_node (loc H_lt_right_fx_fy'))  
                                                     (projT1 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3))
                                                     (projT1 (projT2 (move_foldright (object_at_node (loc H_lt_right_fx_fy')) list_E2_2 E2_3)))
H_same_object_at_node)
              as (M & f' & H_term_arrow_f' & H_eq_f'x & H_eq_f'y' & H_eq_f'y & H_cumul_lt_right_A & H_cumul_lt_left_M & IHx_par_node_is_lettery & IHx_par_object_at_node & IHx_cats_self).

            assert (H_lt_right_once_fx_fy'_rewrite: lt_right_once ( H_term_arrow_f' ((lem070 (multi_bracket_left E1 (object_at_node (loc H_lt_right_fx_fy')) (projT1 mfr) (projT1 (projT2 mfr))) H_same_object_at_node) (self (object_at_node (f x)))) )
 ( H_term_arrow_f' ((lem070 (multi_bracket_left E1 (object_at_node (loc H_lt_right_fx_fy')) (projT1 mfr) (projT1 (projT2 mfr))) H_same_object_at_node) (loc H_lt_right_fx_fy')) ) ).
            {
              rewrite 2lem060.
              apply lem232.

              Lemma lem063 A A' (H_objects_same : objects_same A A') (x y : nodes A) (H_lt_right_once_x_y : lt_right_once x y)
              : lt_right_once (nodes_map H_objects_same x) (nodes_map H_objects_same y).

                apply lem090; assumption. (**/!\LOL already proved at lem090 above**)
              Defined.
              Hint Resolve lem063.

              apply lem063.
              exact H_lt_right_once_fx_fy'_loc.
            }
            (**/!\BUG COQ. fold mfr in H_term_arrow_f', H_eq_f'x, H_eq_f'y', H_eq_f'y |-. alone will make following [rewrite] fail**)

            fold mfr in H_term_arrow_f', H_eq_f'x, H_eq_f'y', H_eq_f'y, H_lt_right_once_fx_fy'_rewrite |- .
            rewrite <- H_eq_f'x in H_lt_right_once_fx_fy'_rewrite.
            erewrite <- H_eq_f'y' in H_lt_right_once_fx_fy'_rewrite by eassumption.
            (**>>>>>>>>>>>>>>>FINALLY WE HAVE lt_right_once f'fx f'fy' YEAH<<<<<<<<<<<<<<<<**)

            (** __START OLD__

Definition multi_bracket_left_topfold E A B_list C : arrows (E /\ (A /\\ (C :: B_list))) ((E /\ A) /\\ (C :: B_list)).

assert (J1 := objects_eq_same (objects_same_cons2 (objects_same_refl E) (projT2 (projT2(move_foldright A B_list C))))).
lazy beta in J1.

assert (J2 := objects_eq_same (projT2 (projT2(move_foldright (E /\ A) B_list C)))).
lazy beta in J2.

rewrite <- J1.
rewrite <- J2.
Lemma lem088 E A B_list : forall C, projT1 (move_foldright (E /\ A) B_list C) = projT1 (move_foldright (A) B_list C).
induction B_list; intros; simpl; 
[ reflexivity
| apply IHB_list
].
Defined.
Hint Resolve lem088.
Hint Rewrite lem088 using eauto.
Lemma lem089 E A B_list : forall C, projT1(projT2 (move_foldright (E /\ A) B_list C)) = projT1(projT2 (move_foldright (A) B_list C)).
induction B_list; intros; simpl; 
[ reflexivity
| f_equal; apply IHB_list
].
Defined.
Hint Resolve lem089.
Hint Rewrite lem089 using eauto.

Show.
(*/!\ALT:  autorewrite * with core using eauto. (*YES!*)*)
(*Fail rewrite lem088. (*because (projT1 (projT2 (t))) has (projT1 t) in its type*)*)
rewrite lem089.
rewrite lem088.
exact (multi_bracket_left E A  (projT1 (move_foldright A B_list C))
      (projT1 (projT2 (move_foldright A B_list C)))).
Defined.
Hint Unfold multi_bracket_left_topfold.

Lemma lem82 (E A C : objects): 
 multi_bracket_left_topfold E A nil C = multi_bracket_left E A C nil. 
unfold multi_bracket_left_topfold.
unfold multi_bracket_left.
simpl  (projT1 (projT2 (move_foldright A nil C)));
simpl (projT1 (move_foldright A nil C)).
Arguments solution_left /.
Arguments block /.
Arguments eq_rect_r /.
Arguments eq_rect /.
Arguments eq_rec_r /.
Arguments eq_rec /.
Arguments eq_ind_r /.
Arguments eq_ind /.
unfold solution_left.
unfold block.
unfold eq_rect_r.
unfold eq_rect.
unfold eq_rec_r.
unfold eq_rec.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_rect.
unfold eq_rect_r.
unfold eq_rect.
unfold eq_rec_r.
unfold eq_rec.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_rect.
simpl.
compute. Abort. 

Lemma lem083 A B Clist : forall D,
 nodes_map (projT2(projT2(move_foldright (A /\ B) Clist D))) ( 
(multi_bracket_left A B (projT1 (move_foldright (A /\ B) Clist D)) (projT1 (projT2 (move_foldright (A /\ B) Clist D))))
 ( at_right A ( foldrightn (foldrightn_self B ((projT1 (move_foldright (A /\ B) Clist D)) :: nil)) (projT1 (projT2 (move_foldright (A /\ B) Clist D))) ) ) ) =
(multi_bracket_left_topfold A B Clist D)
( nodes_map (objects_same_cons2 (objects_same_refl A) (projT2(projT2(move_foldright B Clist D))))
( at_right A ( foldrightn (foldrightn_self B ((projT1 (move_foldright (B) Clist D)) :: nil)) (projT1 (projT2 (move_foldright (B) Clist D))) ) ) ).

__END OLD__ 
             **)

            (**STEP**)
            assert (H_object_at_node_y' : object_at_node y' = object_at_node (f' (f y'))).
            {
              assert (H_object_at_node_fy' : object_at_node (f y') = object_at_node (f' (f y'))).
              { (**/!\NO INSTANTIATED EVAR erewrite H_eq_f'y' by (eexact H_lt_right_fx_fy'). **)
                rewrite (H_eq_f'y' _ H_lt_right_fx_fy').
                SearchPattern (arrows_assoc_on_nodes (multi_bracket_left _ _ _ _) (at_right _ _)).
                rewrite <- (fun H x => objects_eq_same (objects_same_term_arrow_post1 H x)).
                simpl.
                rewrite lem072.
                erewrite lem061 by (eexact H_list_E2_nodes).
                Lemma lem064 (A B C : objects) (Dlist : list objects) 
                : object_at_node ( (multi_bracket_left A B C Dlist) ( at_right A ( foldrightn (foldrightn_self B (C :: nil)) Dlist ) ) ) = B .

                  induction Dlist as [ | E Dlist].
                  - compute. auto.
                  - unfold multi_bracket_left (*autounfold*). autorewrite * with core using eauto (*rewrite lem081*).
                Defined. Hint Resolve lem064. Hint Rewrite lem064 using eauto.
                rewrite lem064.
                symmetry; apply lem121.
              }
              assert (H_object_at_node_y'_pre : object_at_node y' = object_at_node (f y')) by auto (* apply H_object_at_node; exact xyy'_prop_4)*).
              transitivity (object_at_node (f y')); assumption.
            }

            (**STEP**)
            assert (H_object_at_node_y : object_at_node y = object_at_node (f' (f y))).
            {
              assert (H_object_at_node_fy : object_at_node (f y) = object_at_node (f' (f y))).
              { (**/!\NO INSTANTIATED EVAR erewrite H_eq_f'y' by (eexact H_lt_right_fx_fy'). **)
                assert (H_lt_left_fx_fy : lt_left (f x) (f y)) by auto.
                rewrite (H_eq_f'y _ H_lt_left_fx_fy).
                rewrite <- (fun H x => objects_eq_same (objects_same_term_arrow_post1 H x)).
                simpl.
                rewrite lem072.
                assert (lt_left_once (self _) (loc' H_lt_left_fx_fy)) by auto.
                assert (lt_left_once (self _) ((nodes_map (objects_same_sym H_same_object_at_node) (loc' H_lt_left_fx_fy)))) by (rewrite <- (lem091  (objects_same_sym H_same_object_at_node)); auto).
                Lemma lem065 A B (x : nodes (A /\ B)) (H_lt_left_once : lt_left_once (self _) x) : x = (at_left (self A) _).
                  dependent induction H_lt_left_once; simpl; auto. (** :D 1 attempt only FYEAH! **)
                Defined.
                Hint Resolve lem065.
                Hint Rewrite lem065 using auto.
                Lemma lem066 A B C Dlist (x : nodes (A /\ ((B /\ C) /\\ Dlist))) (H_lt_left_once : lt_left_once (self _) x)
                : object_at_node ((multi_bracket_left A B C Dlist) x) = object_at_node x.
                  rewrite (lem065 H_lt_left_once). simpl. clear H_lt_left_once x.
                  induction Dlist as [ | D0 Dlist].
                  - simpl. reflexivity.
                  - simpl. apply IHDlist.
                Defined.
                Hint Resolve lem066. Hint Rewrite lem066 using auto.
                rewrite lem066 by assumption.
              (**/!\BUG Fail rewrite (lem065 H0). (**NONO 7000 lines Set Printing All. Show.**) **)
                assert (Htemp1 := (lem065 H0)).
                simpl in Htemp1. rewrite Htemp1. clear Htemp1.
                simpl.
                Lemma lem067 E A B (x : nodes E) (H_eq : (A/\B) = object_at_node x) (y : nodes E) (H_lt_left_once : lt_left_once x y) : object_at_node y = A.
                  induction x.
                  -  simpl in *. subst. rewrite (lem065 H_lt_left_once). reflexivity.
                  - dependent destruction H_lt_left_once. simpl in *. apply IHx; assumption. 
                  - dependent destruction H_lt_left_once. simpl in *. apply IHx; assumption.                   
                Defined. Hint Resolve lem067. Hint Rewrite lem067 using assumption.
                Show.
                rewrite (lem067 H_object_at_node_fx) by assumption.  reflexivity.
              }
              assert (H_object_at_node_y_pre : object_at_node y = object_at_node (f y)) by auto (* apply H_object_at_node; exact xyy'_prop_4)*).
              transitivity (object_at_node (f y)); assumption.
            }

            (**STEP**)
            assert (H_node_is_lettery_y'_full : node_is_lettery (com_assoc f f') y').
            {
              Lemma lem068 A0 A1 (f0 : arrows_assoc A0 A1) (x : nodes A0) (H_node_is_lettery_f0_x : node_is_lettery f0 x) A2 (f1 : arrows_assoc A1 A2) (H_node_is_lettery_f1_f0x : node_is_lettery f1 (f0 x)) 
              : node_is_lettery (com_assoc f0 f1) x.

                split.
                - simpl. intros y H_lt_leftorright_eq_x_y.
                  (*ALT: intuition.*)
                  apply H_node_is_lettery_f1_f0x. apply H_node_is_lettery_f0_x. assumption.
                - simpl. intros y H_lt_leftorright_eq_x_y.
                  replace ((rev f1) (f1 (f0 x))) with (f0 x) in H_node_is_lettery_f1_f0x |- * by auto.
                  replace ((rev f1) (f1 (f0 y))) with (f0 y) by auto.
                  apply H_node_is_lettery_f0_x. 
                  replace (f0 y) with ((rev f1) (f1 (f0 y))) by auto.
                  apply H_node_is_lettery_f1_f0x. assumption.
              Defined.
              Hint Resolve lem068.

              (**cats where here**)
              (**/!\ lem058 is held to prove [(*H_node_is_lettery_ft :=*) : node_is_lettery f' (f t)] below,
                       ?? lem058 could be held to prove [assert (H_node_is_lettery_fy : node_is_lettery f' (f y)).] and
                       [assert (H_node_is_lettery_fy' : node_is_lettery f' (f y')).] instead of to proving immediately ?? **)
              Lemma lem058  A' B' (f' : arrows A' B') A B (f : arrows A B)(H_term_arrow_f'_f : term_arrow f' f)
                    (x : nodes A') (H_node_is_lettery : node_is_lettery f' x)
              : node_is_lettery f (cats H_term_arrow_f'_f x).
                split.
                - destruct H_node_is_lettery as (H_node_is_lettery & _).
                  induction H_term_arrow_f'_f.
                  + simpl. assumption.
                  + simpl cats. intros y. dependent destruction y.
                    * intros [Htemp | [Htemp | Htemp]]; dependent destruction Htemp.
                    * intros J1. simpl.
                      cut (lt_leftorright_eq ( (f (cats H_term_arrow_f'_f x))) (f y) ) ;
                        [ auto | idtac ].
                      apply IHH_term_arrow_f'_f.
                      destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto. 
                    * intros [Htemp | [Htemp | Htemp]]; dependent destruction Htemp.
                  + simpl cats. intros y. dependent destruction y.
                    * intros [Htemp | [Htemp | Htemp]]; dependent destruction Htemp.
                    * intros [Htemp | [Htemp | Htemp]]; dependent destruction Htemp.
                    * intros J1. simpl.
                      cut (lt_leftorright_eq ( (f (cats H_term_arrow_f'_f x))) (f y) ) ;
                        [ auto | idtac ].
                      apply IHH_term_arrow_f'_f.
                      destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto. 
                - (**this case is copy-paste same as case above, simplly adding [rev f] in the two [cut] lines**)
                  destruct H_node_is_lettery as (_ & H_node_is_lettery).
                  induction H_term_arrow_f'_f.
                  + simpl. assumption.
                  + simpl cats. intros y. dependent destruction y.
                    * intros [Htemp | [Htemp | Htemp]]; dependent destruction Htemp.
                    * intros J1. simpl.
                      cut (lt_leftorright_eq ( (rev f) (f (cats H_term_arrow_f'_f x))) ((rev f) (f y)) ) ;
                        [ auto | idtac ].
                      apply IHH_term_arrow_f'_f.
                      destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto. 
                    * intros [Htemp | [Htemp | Htemp]]; dependent destruction Htemp.
                  + simpl cats. intros y. dependent destruction y.
                    * intros [Htemp | [Htemp | Htemp]]; dependent destruction Htemp.
                    * intros [Htemp | [Htemp | Htemp]]; dependent destruction Htemp.
                    * intros J1. simpl.
                      cut (lt_leftorright_eq ( (rev f) (f (cats H_term_arrow_f'_f x))) ((rev f) (f y)) ) ;
                        [ auto | idtac ].
                      apply IHH_term_arrow_f'_f.
                      destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto. 
              Defined.
              Hint Resolve lem058.

              (** re-memorize that bracket_left_on_nodes sometimes lack one destruction on the node argument before return and sometimes lack two destructions on the node argument before return **)
              Arguments bracket_left_on_nodes : simpl nomatch.

              Lemma lem057 A B C Dlist 
              : node_is_lettery (multi_bracket_left A B C Dlist) (at_right A (foldrightn (foldrightn_self B (C :: nil)) Dlist)).
                  
                split.
                - induction Dlist as [ | D0 Dlist].
                  + simpl.
                    Arguments bracket_left_on_nodes : simpl nomatch (*harmless repeat*). 
                    intros y [J1 | [J1 | J1]]; dependent destruction y; dependent destruction J1; simpl bracket_left_on_nodes; auto (*some goals are solved here*); dependent destruction y; dependent destruction J1; simpl bracket_left_on_nodes; auto.
                  + simpl multi_bracket_left. simpl foldright in *. simpl foldrightn in *.
                    simpl (arrows_assoc_on_nodes ( _ ) (at_right _ _)).
                    intros y J1.
                    dependent destruction y.
                    * destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1.
                    * destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1.
                    * { dependent destruction y.
                        - destruct J1 as [J1 | [J1 | J1]]; do 2 dependent destruction J1.
                        - simpl (arrows_assoc_on_nodes (_) (at_right _ (at_left _ _) )).
                          cut (lt_leftorright_eq
                                 ( ((projT1 (multi_bracket_left_specif A B C Dlist))
                                      (at_right A (foldrightn (at_left (self B) C) Dlist))) )
                                 ( ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_right A y)) ) ) ; [ auto | idtac].
                          apply IHDlist.
                          destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto (* eq case is solve here *); dependent destruction J1; auto.
                        - destruct J1 as [J1 | [J1 | J1]]; do 2 dependent destruction J1.
                      }
                - intros y J1. replace ((rev (multi_bracket_left A B C Dlist))
                                          ((multi_bracket_left A B C Dlist)
                                             (at_right A (foldrightn (foldrightn_self B (C :: nil)) Dlist)))) with (at_right A (foldrightn (foldrightn_self B (C :: nil)) Dlist)) by auto.
                  replace ((rev (multi_bracket_left A B C Dlist))
                             ((multi_bracket_left A B C Dlist) y)) with y by auto.
                  revert y J1.
                  induction Dlist as [ | D0 Dlist].
                  + simpl.
                    Arguments bracket_left_on_nodes : simpl nomatch (*harmless repeat*). 
                    (**ALT : intros y [J1 | [J1 | J1]]; dependent destruction y; dependent destruction J1; simpl bracket_left_on_nodes in *; auto (*some goals are solved here*); (try dependent destruction y); (dependent destruction x || dependent destruction J1); simpl bracket_left_on_nodes in *; auto. **)
                    intros y [J1 | [J1 | J1]]; dependent destruction y (* 9 cases here*); simpl bracket_left_on_nodes in *; (solve [dependent destruction J1] (**/!\ some bad dep dest on eq J1 will change the name from J1 to x**) || (try dependent destruction y; simpl bracket_left_on_nodes in *; dependent destruction J1; auto; dependent destruction J1; auto)).
                  + simpl multi_bracket_left. simpl foldright in *. simpl foldrightn in *.
                    simpl (arrows_assoc_on_nodes ( _ ) (at_right _ _)).
                    intros y J1.
                    dependent destruction y.
                    * simpl (arrows_assoc_on_nodes ( _ ) (self _)) in J1.
                      elimtype Empty_set; apply (lem009700_pre'''' J1).
                      right; constructor.
                      assert (J2 := lem080 A B C Dlist) (**/!\ name lem080**). auto.
                    * simpl (arrows_assoc_on_nodes ( _ ) (at_left _ _)) in J1.
                      elimtype Empty_set. 

                      Lemma lem056 A (y : nodes A) B C Dlist
                      : lt_par ( (multi_bracket_left A B C Dlist) (at_left y ((B /\ C) /\\ Dlist)) )
                               ( (multi_bracket_left A B C Dlist) (at_right A (foldrightn (at_left (self B) C) Dlist)) ).

                        induction Dlist as [ | D0 Dlist].
                        - simpl. auto.
                        - simpl. constructor. apply IHDlist.
                      Defined.
                      Hint Resolve lem056.

                      apply (lem007200 (inl (@lem056 A y B C Dlist))).
                      destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto.
                    * { dependent destruction y.
                        - simpl (arrows_assoc_on_nodes ( _ ) (at_right _ _)) in J1.
                          destruct J1 as [J1 | [J1 | J1]]; do 2 dependent destruction J1.
                        - simpl (arrows_assoc_on_nodes (_) (at_right _ (at_left _ _) )) in J1. (** :D TWISTED FYEAH **)
                          cut ( lt_leftorright_eq (foldrightn (at_left (self B) C) Dlist) y );
                            [ auto 
                            | idtac ].
                          cut ( lt_leftorright_eq (at_right A (foldrightn (at_left (self B) C) Dlist)) (at_right A y) );
                            [ intros [J2 | [J2 | J2]]; dependent destruction J2; auto 
                            | idtac ].
                          apply IHDlist.
                          destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto.
                        - simpl (arrows_assoc_on_nodes (_) (at_right _ (at_right _ _) )) in J1.
                          assert (J3 : lt_par
                                         (at_left
                                            ((projT1 (multi_bracket_left_specif A B C Dlist))
                                               (at_right A (foldrightn (at_left (self B) C) Dlist))) D0)
                                         (at_right (((A /\ B) /\ C) /\\ Dlist) (unitt_on_nodes y))) by auto.
                          elimtype Empty_set. apply (lem007200 (inl J3)).
                          destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto.
                      }
              Defined. Hint Resolve lem057.

              (**with lem064**)
              Lemma lem030 (A B C : objects) (Dlist : list objects) 
              : object_at_node ( ( at_right A ( foldrightn (foldrightn_self B (C :: nil)) Dlist ) ) ) = B .
                   
                induction Dlist; simpl in *; auto.
              Defined.
              Hint Resolve lem030. Hint Rewrite lem030 using eauto.

              Check eq_rect_r.
              Lemma lem029 A B C Dlist (z : nodes B)
              : (multi_bracket_left A B C Dlist)  (loc_rev  (at_right A (foldrightn (at_left (self B) C) Dlist)) (eq_rect_r nodes z (lem030 A B C Dlist)))  =  loc_rev ( (multi_bracket_left A B C Dlist) (at_right A (foldrightn (at_left (self B) C) Dlist)) ) (eq_rect_r nodes z (lem064 A B C Dlist)).

                induction Dlist as [ | D0 Dlist].
                - simpl. reflexivity.
                - simpl. f_equal. apply IHDlist.
              Defined. Hint Resolve lem029. Hint Rewrite lem029 using eauto.

              Lemma lem057' A B C Dlist 
              : forall (z : nodes B), node_is_lettery (multi_bracket_left A B C Dlist) (at_right A (foldrightn (at_left z C) Dlist)).

                induction z as [B | B1 z IHz B2 | B1 B2 z IHz].
                Focus 1. 
                { intros. apply lem057. } Unfocus.
                Focus 2. 
                { split.
                  + intros x J1.
                    assert (H_lt_right_z : lt_right (at_right A (foldrightn (at_left (self (B1/\B2)) C) Dlist)) (at_right A (foldrightn (at_left (at_right B1 z) C) Dlist)) ) by (clear IHz x J1; constructor; induction Dlist; simpl in *; auto).
                    assert (H_lt_right_x : lt_right (at_right A (foldrightn (at_left (self (B1/\B2)) C) Dlist)) x)
                      by (intros; eapply lem00710'; eassumption).
                    
                    Lemma lem027 (*is masked lem051 below*) A (x y z : nodes A) (H_lt_right_x_y : lt_right x y) (H_lt_right_x_z : lt_right x z) (H_lt_leftorright_eq_y_z : lt_leftorright_eq y z) : lt_leftorright_eq (loc H_lt_right_x_y) (loc H_lt_right_x_z).
                      
                      induction H_lt_right_x_y; dependent destruction H_lt_right_x_z; destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]]; dependent destruction H_lt_leftorright_eq_y_z; simpl in *; auto. (** :) 1 ATTEMPT only **)
                    Defined. Hint Resolve lem027.
                      
                    assert (J1_loc : lt_leftorright_eq (loc H_lt_right_z) (loc H_lt_right_x)) by auto.
                    replace ((at_right A (foldrightn (at_left (at_right B1 z) C) Dlist))) with (loc_rev _ (loc H_lt_right_z)) by auto.
                    replace ( x  ) with ( loc_rev _ (loc H_lt_right_x) ) by auto.
                    (* rewrite lem029. *)

                    Lemma lem026 (A : Type) (x : A) (P : A -> Type)(Px : P x)(y: A)(H : x = y) : @eq_rect_r A y P (@eq_rect A x P Px y H) x H = Px.
                      destruct H; reflexivity.
                    Defined. Hint Resolve lem026. Hint Rewrite lem026.

                    rewrite <- (lem026 (nodes) (loc H_lt_right_z) (lem030 A (B1/\B2) C Dlist ) ).
                    rewrite <- (lem026 (nodes) (loc H_lt_right_x) (lem030 A (B1/\B2) C Dlist ) ).
                    rewrite 2!lem029.
                    SearchPattern (lt_right (loc_rev _ _) (loc_rev _ _)). (*return lem231*)

                    Lemma lem025 (A : objects) (fx : nodes A) (fy'_loc : nodes (object_at_node fx)) (fw_loc : nodes (object_at_node fx)) (H_lt_leftorright_eq : lt_leftorright_eq fw_loc fy'_loc)
                    : lt_leftorright_eq (loc_rev fx fw_loc) (loc_rev fx fy'_loc).

                      induction fx; decompose sum H_lt_leftorright_eq; (*destruct H_lt_leftorright_eq as [H_lt_leftorright_eq | [H_lt_leftorright_eq | H_lt_leftorright_eq]]*) simpl; auto. (** :D 1 attempt only, I am too good for this :D **)
                    Defined. Hint Resolve lem025.

                    eapply lem025.

                    Print Implicit eq_rect.
                    Lemma lem024 A (x y : nodes A) B (H : A = B) (H_lt_leftorright_eq_x_y : lt_leftorright_eq x y) : lt_leftorright_eq (eq_rect A nodes x B H) (eq_rect A nodes y B H).

                      destruct H; simpl; assumption.
                    Defined. Hint Resolve lem024.

                    Print Implicit eq_rect_r.
                    Lemma lem023 A (x y : nodes A) B (H : B = A) (H_lt_leftorright_eq_x_y : lt_leftorright_eq x y) : lt_leftorright_eq (eq_rect_r nodes x H) (eq_rect_r nodes y H).

                      destruct H; simpl; assumption.
                    Defined. Hint Resolve lem023.

                    apply lem023. apply lem024. assumption.
                  + {
                      Lemma lem022 A B C Dlist (z : nodes B)
                      : (rev (multi_bracket_left A B C Dlist))  (loc_rev ((multi_bracket_left A B C Dlist) (at_right A (foldrightn (at_left (self B) C) Dlist))) (eq_rect_r nodes z (lem064 A B C Dlist)))  =  loc_rev ( (at_right A (foldrightn (at_left (self B) C) Dlist)) ) (eq_rect_r nodes z (lem030 A B C Dlist)).

                        induction Dlist as [ | D0 Dlist].
                        - simpl. reflexivity.
                        - simpl in IHDlist |- *. rewrite IHDlist. reflexivity.
                      Defined. Hint Resolve lem022. Hint Rewrite lem022 using eauto.

                      assert (H_lt_right_z : lt_right ( ((multi_bracket_left A (B1 /\ B2) C Dlist) (at_right A (foldrightn (at_left (self (B1/\B2)) C) Dlist))) ) ( ((multi_bracket_left A (B1 /\ B2) C Dlist) (at_right A (foldrightn (at_left (at_right B1 z) C) Dlist))) )) 
                        by (clear IHz; induction Dlist; simpl in *; auto).
                      intros x J1.
                      assert (H_lt_right_x : lt_right ( ((multi_bracket_left A (B1 /\ B2) C Dlist) (at_right A (foldrightn (at_left (self (B1/\B2)) C) Dlist))) ) ( ((multi_bracket_left A (B1 /\ B2) C Dlist) x) )) 
                        by (intros; eapply lem00710'; eassumption).
                      assert (J1_loc : lt_leftorright_eq (loc H_lt_right_z) (loc H_lt_right_x)) by auto.

                      replace  ((multi_bracket_left A (B1 /\ B2) C Dlist) (at_right A (foldrightn (at_left (at_right B1 z) C) Dlist))) with (loc_rev _ (loc H_lt_right_z)) by auto.
                      replace ( ((multi_bracket_left A (B1 /\ B2) C Dlist) x) ) with ( loc_rev _ (loc H_lt_right_x) ) by auto.
                      rewrite <- (lem026 (nodes) (loc H_lt_right_z) (lem064 A (B1/\B2) C Dlist ) ).
                      rewrite <- (lem026 (nodes) (loc H_lt_right_x) (lem064 A (B1/\B2) C Dlist ) ).
                      rewrite 2!lem022.
                      eapply lem025.
                      apply lem023. apply lem024. assumption.
                    }
                } Unfocus.
               Focus 1. 
               {
                 split.
                 + intros x J1.
                   assert (H_lt_left_z : lt_left (at_right A (foldrightn (at_left (self (B1/\B2)) C) Dlist)) (at_right A (foldrightn (at_left (at_left z B2) C) Dlist)) ) 
                     by (clear IHz x J1; constructor; induction Dlist; simpl in *; auto).
                   assert (H_lt_left_x : lt_left (at_right A (foldrightn (at_left (self (B1/\B2)) C) Dlist)) x)
                     by (intros; eapply lem00710''; eassumption).

                   Lemma lem021 A (x y z : nodes A) (H_lt_left_x_y : lt_left x y) (H_lt_left_x_z : lt_left x z) (H_lt_leftorright_eq_y_z : lt_leftorright_eq y z) : lt_leftorright_eq (loc' H_lt_left_x_y) (loc' H_lt_left_x_z).
                      
                     induction H_lt_left_x_y; dependent destruction H_lt_left_x_z; destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]]; dependent destruction H_lt_leftorright_eq_y_z; simpl in *; auto. (** :) 1 ATTEMPT only **)
                   Defined. Hint Resolve lem021.
                      
                   assert (J1_loc : lt_leftorright_eq (loc' H_lt_left_z) (loc' H_lt_left_x)) by auto.

                   Lemma lem543' (A : objects) (x : nodes A) (y : nodes A) (H_lt_left_x_y : lt_left x y):  loc_rev x (loc' H_lt_left_x_y) = y.
                     induction x; dependent destruction H_lt_left_x_y;
                     [ simpl; reflexivity
                     | simpl; rewrite IHx; reflexivity ..
                     ].          
                   Defined.
                   Hint Resolve lem543'.

                   replace ((at_right A (foldrightn (at_left (at_left z B2) C) Dlist))) with (loc_rev _ (loc' H_lt_left_z)) by auto.
                   replace ( x  ) with ( loc_rev _ (loc' H_lt_left_x) ) by auto.
                   (* rewrite lem029. *)

                   rewrite <- (lem026 (nodes) (loc' H_lt_left_z) (lem030 A (B1/\B2) C Dlist ) ).
                   rewrite <- (lem026 (nodes) (loc' H_lt_left_x) (lem030 A (B1/\B2) C Dlist ) ).
                   rewrite 2!lem029.
                   
                   eapply lem025.
                   
                   apply lem023. apply lem024. assumption.
                 + 
                   assert (H_lt_left_z : lt_left ( ((multi_bracket_left A (B1 /\ B2) C Dlist) (at_right A (foldrightn (at_left (self (B1/\B2)) C) Dlist))) ) ( ((multi_bracket_left A (B1 /\ B2) C Dlist) (at_right A (foldrightn (at_left (at_left z B2) C) Dlist))) )) 
                     by (clear IHz; induction Dlist; simpl in *; auto).
                   intros x J1.
                   assert (H_lt_left_x : lt_left ( ((multi_bracket_left A (B1 /\ B2) C Dlist) (at_right A (foldrightn (at_left (self (B1/\B2)) C) Dlist))) ) ( ((multi_bracket_left A (B1 /\ B2) C Dlist) x) )) 
                     by (intros; eapply lem00710''; eassumption).
                   assert (J1_loc : lt_leftorright_eq (loc' H_lt_left_z) (loc' H_lt_left_x)) by auto.

                   replace  ((multi_bracket_left A (B1 /\ B2) C Dlist) (at_right A (foldrightn (at_left (at_left z B2) C) Dlist))) with (loc_rev _ (loc' H_lt_left_z)) by auto.
                   replace ( ((multi_bracket_left A (B1 /\ B2) C Dlist) x) ) with ( loc_rev _ (loc' H_lt_left_x) ) by auto.
                   rewrite <- (lem026 (nodes) (loc' H_lt_left_z) (lem064 A (B1/\B2) C Dlist ) ).
                   rewrite <- (lem026 (nodes) (loc' H_lt_left_x) (lem064 A (B1/\B2) C Dlist ) ).
                   rewrite 2!lem022.
                   eapply lem025.
                   apply lem023. apply lem024. assumption. } Unfocus.
              Defined.
              Hint Resolve lem057'.
               
              Lemma lem057_post2 A B C Dlist (z : nodes (A /\ ((B /\ C) /\\ Dlist))) (H_lt_leftorright_eq_self_z : lt_leftorright_eq (at_right A (foldrightn (at_left (self B) C) Dlist)) z) 
              : node_is_lettery (multi_bracket_left A B C Dlist) z.

                destruct H_lt_leftorright_eq_self_z as [H_lt_leftorright_eq_self_z | [H_lt_leftorright_eq_self_z | H_lt_leftorright_eq_self_z]].
                - replace z. apply lem057.
                - Check lem030. 
                  Lemma lem020 A B C Dlist (z_loc : nodes (object_at_node (at_right A (foldrightn (foldrightn_self B (C :: nil)) Dlist))))
                  : loc_rev (at_right A (foldrightn (at_left (self B) C) Dlist)) z_loc = (at_right A (foldrightn (at_left ((eq_rect _ nodes z_loc _ (lem030 A B C Dlist))) C) Dlist)) .
                    induction Dlist as [ | D0 Dlist]. 
                    - simpl. reflexivity. 
                    - simpl lem030. simpl. f_equal.  f_equal.
                      cut ( at_right A (loc_rev (foldrightn (at_left (self B) C) Dlist) z_loc) =
                            at_right A (foldrightn
                                          (at_left
                                             (eq_rect _ nodes z_loc _ (lem030 A B C Dlist)) C) Dlist) ); [intros J1; dependent destruction J1; auto | idtac].
                      simpl in z_loc. apply IHDlist.
                  Defined. Hint Resolve lem020. Hint Rewrite lem020 using eauto.

                  replace (z) with ( loc_rev _ (loc' H_lt_leftorright_eq_self_z) ) by auto.
                  rewrite lem020.
                  apply lem057'.
                - replace (z) with ( loc_rev _ (loc H_lt_leftorright_eq_self_z) ) by auto.
                  rewrite lem020.
                  apply lem057'.
              Defined.
              Hint Resolve lem057_post2.

              Lemma lem055 A B C Dlist 
              : node_is_lettery (multi_bracket_left A B C Dlist) (at_left (self A) _). 

                split.
                - induction Dlist as [ | D0 Dlist].
                  + simpl.
                    Arguments bracket_left_on_nodes : simpl nomatch (*harmless repeat*). 
                    intros y [J1 | [J1 | J1]]; dependent destruction y; dependent destruction J1; simpl bracket_left_on_nodes; auto (*some goals are solved here*); dependent destruction y; dependent destruction J1; simpl bracket_left_on_nodes; auto.
                  + simpl multi_bracket_left. simpl foldright in *. simpl foldrightn in *.
                    simpl (arrows_assoc_on_nodes ( _ ) (at_left _ _)).
                    intros y J1.
                    dependent destruction y.
                    * destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1.
                    * simpl (arrows_assoc_on_nodes ( _ ) (at_left _ _)).
                      cut ( lt_leftorright_eq
                              ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_left (self A) ((B /\ C) /\\ Dlist)))
                              ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_left y ((B /\ C) /\\ Dlist))) ); 
                        [ auto | idtac ].

                      Lemma lem054 A (y : nodes A) B C Dlist
                      : lt_leftorright_eq  ((multi_bracket_left A B C Dlist) (at_left (self A) ((B /\ C) /\\ Dlist))) ((multi_bracket_left A B C Dlist) (at_left y ((B /\ C) /\\ Dlist))).
                        induction Dlist as [ | D0 Dlist].
                        - simpl. cut (lt_leftorright_eq (self A) y); auto (*using some lemma above..*).
                        - simpl. cut ( lt_leftorright_eq
                                         ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_left (self A) ((B /\ C) /\\ Dlist)))
                                         ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_left y ((B /\ C) /\\ Dlist))) );
                                 [ auto | apply IHDlist ].
                      Defined. Hint Resolve lem054.

                      auto (**apply lem054**).
                    * assert (J3 : lt_par (at_left (self A) _) (at_right _ y)) by auto.
                      elimtype Empty_set. apply (lem007200 (inl J3)). auto.
                      (*intuition = *) destruct J1 as [J1 | [J1 | J1]]; auto.
                - intros y J1. replace ( ((rev (multi_bracket_left A B C Dlist))  ((multi_bracket_left A B C Dlist)  (at_left (self A) ((B /\ C) /\\ Dlist)))) )
                               with ( (at_left (self A) ((B /\ C) /\\ Dlist)) ) by auto.
                  replace ( (rev (multi_bracket_left A B C Dlist)) ((multi_bracket_left A B C Dlist) y) )
                  with y by auto.
                  revert y J1.
                  induction Dlist as [ | D0 Dlist].
                  + simpl.
                    Arguments bracket_left_on_nodes : simpl nomatch (*harmless repeat*). 
                    (**/!\ the old ALT: do not solve anymore **)
                    intros y [J1 | [J1 | J1]]; dependent destruction y (* 9 cases here*); simpl bracket_left_on_nodes in *; (solve [dependent destruction J1] (**/!\ some bad dep dest on eq J1 will change the name from J1 to x**) || (try dependent destruction y; simpl bracket_left_on_nodes in *; dependent destruction J1; auto; dependent destruction J1; auto)).                      
                  + simpl multi_bracket_left. simpl foldright in *. simpl foldrightn in *.
                    simpl (arrows_assoc_on_nodes ( _ ) (at_left _ _)).
                    intros y J1.
                    dependent destruction y.
                    * simpl (arrows_assoc_on_nodes ( _ ) (self _)) in J1.
                      elimtype Empty_set.

                      Lemma lem053 A B C Dlist
                      : lt_left_once ((multi_bracket_left A B C Dlist) (self _)) ((multi_bracket_left A B C Dlist) (at_left (self A) _)).
                        induction Dlist as [ | D0 Dlist].
                        - simpl. auto.
                        - simpl. constructor. apply IHDlist.
                      Defined.
                      Hint Resolve lem053.

                      apply (lem009700_pre'''' J1).
                      assert (J2 := lem053 A B C Dlist). auto.
                    * clear J1. auto. (*simpl (arrows_assoc_on_nodes ( _ ) (at_left _ _)) in J1.
                        elimtype Empty_set. 
                        
                        Lemma lem056 A (y : nodes A) B C Dlist
                        : lt_par ( (multi_bracket_left A B C Dlist) (at_left y ((B /\ C) /\\ Dlist)) )
                                 ( (multi_bracket_left A B C Dlist) (at_right A (foldrightn (at_left (self B) C) Dlist)) ).

                          induction Dlist as [ | D0 Dlist].
                          - simpl. auto.
                          - simpl. constructor. apply IHDlist.
                        Defined.
                        Hint Resolve lem056.

                        Show. apply (lem007200 (inl (@lem056 A y B C Dlist))). 
                        destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto.*)
                    * { elimtype Empty_set.
                        dependent destruction y.
                        - simpl (arrows_assoc_on_nodes ( _ ) (at_right _ _)) in J1.
                          destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1.
                        - simpl (arrows_assoc_on_nodes (_) (at_right _ (at_left _ _) )) in J1.

                          Lemma lem052 A B C Dlist (y : nodes ((B /\ C) /\\ Dlist))
                                (H_lt_leftorright_eq : lt_leftorright_eq ( (multi_bracket_left A B C Dlist) (at_left (self A) _) )
                                                ( (multi_bracket_left A B C Dlist) (at_right _ y ) ))
                          : Empty_set.
                            induction Dlist as [ | D0 Dlist].
                            - simpl in y; dependent destruction y;
                              destruct H_lt_leftorright_eq as [H_lt_leftorright_eq | [H_lt_leftorright_eq | H_lt_leftorright_eq]];
                              simpl in *; do 2 dependent destruction H_lt_leftorright_eq.
                            - simpl in y. dependent destruction y. 
                              + destruct  H_lt_leftorright_eq as [ H_lt_leftorright_eq | [ H_lt_leftorright_eq |  H_lt_leftorright_eq ] ]; simpl in H_lt_leftorright_eq; dependent destruction  H_lt_leftorright_eq.
                              + apply (IHDlist y).
                                simpl in H_lt_leftorright_eq. 
                                destruct  H_lt_leftorright_eq as [ H_lt_leftorright_eq | [ H_lt_leftorright_eq |  H_lt_leftorright_eq ] ]; simpl in H_lt_leftorright_eq; dependent destruction  H_lt_leftorright_eq; auto.
                              + simpl in H_lt_leftorright_eq. 
                                destruct  H_lt_leftorright_eq as [ H_lt_leftorright_eq | [ H_lt_leftorright_eq |  H_lt_leftorright_eq ] ]; simpl in H_lt_leftorright_eq; dependent destruction  H_lt_leftorright_eq.
                          Defined. Hint Resolve lem052.

                          apply (@lem052 A B C Dlist y).
                          destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1; auto.
                        - simpl (arrows_assoc_on_nodes ( _ ) (at_right _ _)) in J1.
                          destruct J1 as [J1 | [J1 | J1]]; dependent destruction J1.
                      }
              Defined.
              Hint Resolve lem055.

              Lemma lem055_post1 A B C Dlist 
              : forall (z : nodes A), node_is_lettery (multi_bracket_left A B C Dlist) (at_left (z) _).  

                induction z as [A | A1 z IHz A2 | A1 A2 z IHz].
                Focus 1. 
                { intros. apply lem055. } Unfocus.
                Focus 2. 
                { split.
                  + intros x J1.
                    assert ( H_lt_right_z : lt_right (at_left (self _) ((B /\ C) /\\ Dlist)) (at_left (at_right A1 z) ((B /\ C) /\\ Dlist)) ) by (clear IHz x J1; constructor; induction Dlist; simpl in *; auto).
                    assert (H_lt_right_x : lt_right (at_left (self _) ((B /\ C) /\\ Dlist)) x)
                      by (intros; eapply lem00710'; eassumption).
                      
                    assert (J1_loc : lt_leftorright_eq (loc H_lt_right_z) (loc H_lt_right_x)) by auto.
                    replace ( (at_left (at_right A1 z) ((B /\ C) /\\ Dlist)) ) with (loc_rev _ (loc H_lt_right_z)) by auto.
                    replace ( x  ) with ( loc_rev _ (loc H_lt_right_x) ) by auto.
                    Check lem030. Check lem029.
                    SearchPattern (object_at_node _ = object_at_node _). (*return lem066*)
                    Lemma lem019 A B C Dlist : object_at_node ((multi_bracket_left A B C Dlist)(at_left (self A) ((B/\C)/\\Dlist))) = A. induction Dlist; simpl in *; auto.
                    Defined. Hint Rewrite lem019 using eauto. Hint Resolve lem019.

                    Lemma lem018 A B C Dlist (z : nodes A)
                    : (multi_bracket_left A B C Dlist) (loc_rev (at_left (self A) ((B/\C)/\\Dlist)) z) 
                      = loc_rev ((multi_bracket_left A B C Dlist) (at_left (self A) ((B/\C)/\\Dlist))) (eq_rect_r nodes z (lem019 A B C Dlist)).
                  
                      induction Dlist as [ | D0 Dlist].
                      - simpl. reflexivity.
                      - simpl. f_equal. apply IHDlist.
                    Defined. Hint Resolve lem018. Hint Rewrite lem018 using eauto.

                    rewrite 2!lem018.
                    SearchPattern (lt_right (loc_rev _ _) (loc_rev _ _)). (*return lem231*)
                    eapply lem025.
                    apply lem023. assumption.
                  + {
                      Lemma lem017 A B C Dlist (z : nodes A)
                      : (rev (multi_bracket_left A B C Dlist))  (loc_rev ((multi_bracket_left A B C Dlist) (at_left (self A) ((B/\C)/\\Dlist))) (eq_rect_r nodes z (lem019 A B C Dlist)))  =  loc_rev ( (at_left (self A) ((B/\C)/\\Dlist)) ) z.
                        
                        induction Dlist as [ | D0 Dlist].
                        - simpl. reflexivity.
                        - simpl in IHDlist |- *. rewrite IHDlist. reflexivity.
                      Defined. Hint Resolve lem017. Hint Rewrite lem017 using eauto.

                      assert (H_lt_right_z : lt_right ( ((multi_bracket_left (A1/\A2) B C Dlist) (at_left (self (A1/\A2)) ((B/\C)/\\Dlist))) ) ( ((multi_bracket_left (A1/\A2) B C Dlist) (at_left (at_right A1 z) ((B/\C)/\\Dlist))) )) 
                        by (clear IHz; induction Dlist; simpl in *; auto).
                      intros x J1.
                      assert (H_lt_right_x : lt_right ( ((multi_bracket_left (A1/\A2) B C Dlist) (at_left (self (A1/\A2)) ((B/\C)/\\Dlist))) ) ( ((multi_bracket_left (A1/\A2) B C Dlist) x) )) 
                        by (intros; eapply lem00710'; eassumption).
                      assert (J1_loc : lt_leftorright_eq (loc H_lt_right_z) (loc H_lt_right_x)) by auto.

                      replace  ((multi_bracket_left (A1 /\ A2) B C Dlist) (at_left (at_right A1 z) ((B /\ C) /\\ Dlist)))  with (loc_rev _ (loc H_lt_right_z)) by auto.
                      replace ( ((multi_bracket_left (A1 /\ A2) B C Dlist) x) ) with ( loc_rev _ (loc H_lt_right_x) ) by auto.

                      rewrite <- (lem026 (nodes) (loc H_lt_right_z) (lem019 (A1/\A2) B C Dlist ) ).
                      rewrite <- (lem026 (nodes) (loc H_lt_right_x) (lem019 (A1/\A2) B C Dlist ) ).
                      rewrite 2!lem017.
                      apply lem025.
                      apply lem024. assumption.
                    }
                } Unfocus.
                Focus 1. 
                { split.
                  + intros x J1.
                    assert ( H_lt_left_z : lt_left (at_left (self _) ((B /\ C) /\\ Dlist)) (at_left (at_left z A2) ((B /\ C) /\\ Dlist)) ) by (clear IHz x J1; constructor; induction Dlist; simpl in *; auto).
                    assert (H_lt_left_x : lt_left (at_left (self _) ((B /\ C) /\\ Dlist)) x)
                      by (intros; eapply lem00710''; eassumption).
                    
                    assert (J1_loc : lt_leftorright_eq (loc' H_lt_left_z) (loc' H_lt_left_x)) by auto.
                    replace ( (at_left (at_left z A2) ((B /\ C) /\\ Dlist)) ) with (loc_rev _ (loc' H_lt_left_z)) by auto.
                    replace ( x  ) with ( loc_rev _ (loc' H_lt_left_x) ) by auto.
                    
                    rewrite 2!lem018.
                    SearchPattern (lt_left (loc_rev _ _) (loc_rev _ _)). (*return lem231*)
                    eapply lem025.
                    apply lem023. assumption.
                  + 
                    assert (H_lt_left_z : lt_left ( ((multi_bracket_left (A1/\A2) B C Dlist) (at_left (self (A1/\A2)) ((B/\C)/\\Dlist))) ) ( ((multi_bracket_left (A1/\A2) B C Dlist) (at_left (at_left z A2) ((B/\C)/\\Dlist))) )) 
                      by (clear IHz; induction Dlist; simpl in *; auto).
                    intros x J1.
                    assert (H_lt_left_x : lt_left ( ((multi_bracket_left (A1/\A2) B C Dlist) (at_left (self (A1/\A2)) ((B/\C)/\\Dlist))) ) ( ((multi_bracket_left (A1/\A2) B C Dlist) x) )) 
                      by (intros; eapply lem00710''; eassumption).
                    assert (J1_loc : lt_leftorright_eq (loc' H_lt_left_z) (loc' H_lt_left_x)) by auto.
                    
                    replace  ((multi_bracket_left (A1 /\ A2) B C Dlist) (at_left (at_left z A2) ((B /\ C) /\\ Dlist)))  with (loc_rev _ (loc' H_lt_left_z)) by auto.
                    replace ( ((multi_bracket_left (A1 /\ A2) B C Dlist) x) ) with ( loc_rev _ (loc' H_lt_left_x) ) by auto.
                    
                    rewrite <- (lem026 (nodes) (loc' H_lt_left_z) (lem019 (A1/\A2) B C Dlist ) ).
                    rewrite <- (lem026 (nodes) (loc' H_lt_left_x) (lem019 (A1/\A2) B C Dlist ) ).
                    rewrite 2!lem017.
                    apply lem025.
                    apply lem024. assumption.
                } Unfocus.
              Defined.
              Hint Resolve lem055_post1.

              Lemma lem055_post2 A B C Dlist (z : nodes (A /\ ((B /\ C) /\\ Dlist))) (H_lt_leftorright_eq_self_z : lt_leftorright_eq (at_left (self A) ((B/\C)/\\Dlist)) z) 
              : node_is_lettery (multi_bracket_left A B C Dlist) z.

                destruct H_lt_leftorright_eq_self_z as [H_lt_leftorright_eq_self_z | [H_lt_leftorright_eq_self_z | H_lt_leftorright_eq_self_z]].
                - replace z. apply lem055.
                - { 
                    Lemma lem016 A B C Dlist (z_loc : nodes A) : loc_rev (at_left (self A) ((B/\C)/\\Dlist)) z_loc = (at_left (z_loc) ((B/\C)/\\Dlist)).
                      simpl; reflexivity.
                    Defined. Hint Resolve lem016. Hint Rewrite lem016 using eauto.

                    replace (z) with ( loc_rev _ (loc' H_lt_leftorright_eq_self_z) ) by auto.
                    rewrite lem016.
                    apply lem055_post1.
                  }
                - replace (z) with ( loc_rev _ (loc H_lt_leftorright_eq_self_z) ) by auto.
                  rewrite lem016.
                  apply lem055_post1.
              Defined.
              Hint Resolve lem055_post2.

              (**SUB-STEP**) (**ALT: ?? USE lem058 ??**)
              assert (H_node_is_lettery_fy' : node_is_lettery f' (f y')).
              {
                split.
                - rewrite (H_eq_f'y' _ H_lt_right_fx_fy').
                  intros z J1.
                  assert (J2 : lt_right (f x) z) by (eapply lem00710'; eassumption).
                  rewrite (H_eq_f'y' _ J2).
                  SearchPattern ( lt_right (loc _) (loc _)  ).
                  (*Lemma lem051 A (x y z : nodes A) (H_lt_right_x_y : lt_right x y) (H_lt_right_x_z : lt_right x z) (H_lt_right_y_z : lt_right y z) : lt_right (loc H_lt_right_x_y) (loc H_lt_right_x_z).
                      
                      induction H_lt_right_x_y; dependent destruction H_lt_right_x_z; dependent destruction H_lt_right_y_z; simpl in *; auto. 
                    Defined.*)

                  Lemma lem050 A (x y : nodes A) (H_lt_right_x_y : lt_right x y) (z : nodes A) (H_lt_right_x_z : lt_right x z) (H_lt_leftorright_eq_y_z : lt_leftorright_eq y z) : lt_leftorright_eq (loc H_lt_right_x_y) (loc H_lt_right_x_z).
                      
                    induction H_lt_right_x_y;
                    dependent destruction H_lt_right_x_z;
                    destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]];
                    dependent destruction H_lt_leftorright_eq_y_z; simpl in *; auto. 
                  Defined.
                  Hint Resolve lem050.

                  Lemma lem049 A (x y : nodes A) (H_lt_left_x_y : lt_left x y) (z : nodes A) (H_lt_left_x_z : lt_left x z) (H_lt_leftorright_eq_y_z : lt_leftorright_eq y z) : lt_leftorright_eq (loc' H_lt_left_x_y) (loc' H_lt_left_x_z).
                      
                    induction H_lt_left_x_y;
                    dependent destruction H_lt_left_x_z;
                    destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]];
                    dependent destruction H_lt_leftorright_eq_y_z; simpl in *; auto. 
                  Defined.
                  Hint Resolve lem049.

                  Lemma lem048 A0 A1 (H_objects_same : objects_same A0 A1) (y z : nodes A1) (H_lt_leftorright_eq_y_z : lt_leftorright_eq y z) : lt_leftorright_eq ((lem071 H_objects_same) y) ((lem071 H_objects_same) z).
                    
                    induction H_objects_same.
                    - simpl; assumption.
                    - dependent destruction y; dependent destruction z;
                      destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]];
                      dependent destruction H_lt_leftorright_eq_y_z;
                      simpl in *; auto. (** :D 1 attempt only FYEAH ! :) **)
                  Defined.
                  Hint Resolve lem048.

                  Lemma lem047 A' B' (f' : arrows A' B') A B (f : arrows A B) (H_term_arrow_f'_f : term_arrow f' f) (y z : nodes B') (H_lt_leftorright_eq_y_z : lt_leftorright_eq y z) : lt_leftorright_eq (H_term_arrow_f'_f y) (H_term_arrow_f'_f z).

                    induction H_term_arrow_f'_f;
                    simpl in *; auto.
                  Defined.
                  Hint Resolve lem047.

                  apply lem047.
                  simpl arrows_assoc_on_nodes.

                  SearchPattern (lem071 _ _ = nodes_map _ _). (**ouput lem072**)
                  rewrite (lem072 _ (loc H_lt_right_fx_fy')).
                  SearchPattern (nodes_map (objects_same_sym _) _ = _). (**ouput lem061**)
                  erewrite lem061 by (eexact H_list_E2_nodes (*by eassumption*)).
                  apply lem057.
                  SearchAbout (nodes_map (objects_same_sym _) _ = _). (**ouput lem061**)
                  Print Implicit lem061.
                  rewrite <- (lem061 (H_same_object_at_node) _ (x':= loc H_lt_right_fx_fy')) by (exact H_list_E2_nodes (*by eassumption*)).
                  rewrite <- lem072.
                  cut ( lt_leftorright_eq (loc H_lt_right_fx_fy') (loc J2) ); 
                    [ auto (*intros Htemp; apply lem048; exact Htemp*)
                    | auto (*apply lem050; assumption*) ].
                - {
                    (** clean version with lt_right instead of <r **)
                    Lemma lem033 (*lem001700''''*) A B (f : arrows A B)
                    : forall x y : A, lt_right (f x) (f y) -> lt_right x y.

                      induction f. 
                      - intros x y H; assumption.
                      - simpl; intros x y H; dependent destruction x; dependent destruction y;
                        solve [
                            do 2 dependent destruction H
                          | constructor
                          | do 2 dependent destruction H;
                            constructor;
                            assumption
                          | dependent destruction y;
                            do 2 dependent destruction H
                          | dependent destruction x;
                            do 2 dependent destruction H
                          | dependent destruction x;
                            dependent destruction y;
                            try do 2 dependent destruction H;
                            repeat (constructor; try assumption) ].
                      - simpl in *; intros x y H; dependent destruction x;
                        dependent destruction y;
                        solve [
                            dependent destruction H
                          | constructor
                          | dependent destruction H;
                            constructor; 
                            apply IHf1;
                            assumption
                          | dependent destruction H;
                            constructor; 
                            apply IHf2;
                            assumption ].
                      - simpl in *; intros x y H; apply IHf1; apply IHf2; assumption.
                    Defined. Hint Resolve lem033.

                    (**this lem046 will be used later. also almost copy paste proof commands of lem001700'', here for comparaison only and to prepare for lem044 below**)
                    Lemma lem046 (*lem001700'''*) A B (f : arrows A B)
                    : forall x y : B, lt_left ((rev f) x) ((rev f) y) -> lt_left x y.

                      induction f. 
                      - intros x y H; assumption.
                      - simpl; intros x y H; dependent destruction x; dependent destruction y;
                        solve [
                            do 2 dependent destruction H
                          | constructor
                          | do 2 dependent destruction H;
                            constructor;
                            assumption
                          | dependent destruction y;
                            do 2 dependent destruction H
                          | dependent destruction x;
                            do 2 dependent destruction H
                          | dependent destruction x;
                            dependent destruction y;
                            try do 2 dependent destruction H;
                            repeat (constructor; try assumption) ].
                      - simpl in *; intros x y H; dependent destruction x;
                        dependent destruction y;
                        solve [
                            dependent destruction H
                          | constructor
                          | dependent destruction H;
                            constructor; 
                            apply IHf1;
                            assumption
                          | dependent destruction H;
                            constructor; 
                            apply IHf2;
                            assumption ].
                      - simpl in *; intros x y H; apply IHf2; apply IHf1; assumption.
                    Defined.
                    Hint Resolve lem046.
                    
                    (**this lem036, which used lem046, will be used**)
                    Lemma lem034 (*lem001700''''*) A B (f : arrows A B)
                    : forall x y : A, lt_left ( x) ( y) -> lt_left (f x) (f y).

                      intros x y H_lt_left_x_y.
                      replace x with ((rev f) (f x)) in H_lt_left_x_y by auto.
                      replace y with ((rev f) (f y)) in H_lt_left_x_y by auto.
                      eapply lem046; eassumption. 
                    Defined.
                    Hint Resolve lem034.

                    (**OLD lem045, is replaced by lem044 with corresponding lem043.
                    Lemma lem045 A B C : ( forall x y : nodes ((A /\ B) /\ C), ( x = self _ -> Empty_set) -> lt_left x y -> lt_left ((rev (bracket_left A B C)) x) ((rev (bracket_left A B C)) y) ).
                      
                      intros x y H_x_is_self H_lt_left_x_y.
                      dependent destruction H_lt_left_x_y.
                      + elimtype Empty_set; auto.
                      + dependent destruction H_lt_left_x_y;
                        constructor; auto.
                      + constructor; auto.
                    Defined.
                    Hint Resolve lem045.
                    (** with old lem045, the lem043 below blocks no progress in this part:
                          replace (bracket_right_on_nodes (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) x) D0)) with ((rev (bracket_left A ((B /\ C) /\\ Dlist) D0)) (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) x) D0)) by reflexivity.
                          replace (bracket_right_on_nodes (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) y) D0)) with ((rev (bracket_left A ((B /\ C) /\\ Dlist) D0)) (at_left ((rev (projT1 (multi_bracket_left_specif A B C Dlist))) y) D0)) by reflexivity.
                          apply lem045.
                          * discriminate.
                          * constructor. apply IHDlist. 
                            Focus 2. reflexivity. /!\ NO PROGRESS **)
                     **)
                    
                    (**OLD TOERASE: ATTEMPTS
                     (**
                    Definition nodal_multi_bracket_left'' {A : objects} {x : A} {A2 B2 C2 Dlist2} (H_object_at_node: object_at_node x = up_0 A2 ((B2 /\ C2) /\\ Dlist2))
: { M : objects & { f' : arrows A M & { term_arrow_f_f' : (term_arrow (multi_bracket_left A2 B2 C2 Dlist2) f') & 
prod ( (f' x) = term_arrow_f_f' ((multi_bracket_left A2 B2 C2 Dlist2) (self (A2 /\ ((B2 /\ C2) /\\ Dlist2)))) ) 
( prod (forall n l : nodes A, ( n = x -> Empty_set) -> n <r l -> f' n <r f' l)
      ( forall n l : nodes M, ( lt_left_eq x ((rev f') l) -> Empty_set ) -> lt_left n l -> lt_left ((rev f') n) ((rev f') l) ) ) } } }.

  induction x as [ A | A x IHx B | A B x IHx ].
  - simpl in H_object_at_node; subst A.
    split with (((A2 /\ B2) /\ C2) /\\ Dlist2);
    split with (multi_bracket_left A2 B2 C2 Dlist2).
    split with (term_arrow_self (multi_bracket_left A2 B2 C2 Dlist2)).
    split.
    + auto.
    + auto.
  - 
    split with ((projT1 (IHx H_object_at_node)) /\ B);
    split with ((projT1 (projT2 (IHx H_object_at_node))) /\1 unitt B).
    split with (term_arrow_at_left (projT1(projT2(projT2(IHx H_object_at_node)))) _).
    (**/!\BUG COQ IS VERY SLOW OR INFINITE TO ACCEPT THIS NEXT LINE FOR SIGMA TYPES**)
    destruct (projT2(projT2(projT2(IHx H_object_at_node)))) as (IHx_cat_term_arrow & IHx_nonvariance).
                     **)
                     (**
                    Lemma lem042 A (x : nodes A) A2 B2 C2 Dlist2 (H_object_at_node: object_at_node x = up_0 A2 ((B2 /\ C2) /\\ Dlist2))
: forall n l : nodes (projT1 (nodal_multi_bracket_left H_object_at_node)), 
 ( lt_left_eq x ((rev (projT1(projT2(nodal_multi_bracket_left H_object_at_node)))) l) -> Empty_set )
 -> lt_left n l 
 -> lt_left ((rev (projT1(projT2(nodal_multi_bracket_left H_object_at_node)))) n) ((rev (projT1(projT2(nodal_multi_bracket_left H_object_at_node)))) l).

              induction x as [ A | A x IHx B | A B x IHx ].
              - simpl in H_object_at_node; subst A.
                simpl. apply lem043.
              - specialize IHx with (H_object_at_node:=H_object_at_node).
                replace (projT1 (nodal_multi_bracket_left (x:= at_left x B) H_object_at_node)) with
                ((projT1 (nodal_multi_bracket_left (x := x) H_object_at_node)) /\ B).
                Focus 2. compute; reflexivity. simpl.
                Check ((projT1 (projT2 (nodal_multi_bracket_left (x:= at_left x B) H_object_at_node)))).
                Check (((projT1 (projT2 (nodal_multi_bracket_left (x:= x) H_object_at_node))))).
                (**/!\BUG COQ says non-vertible types at this place **)
                replace ((projT1 (projT2 (nodal_multi_bracket_left (x:= at_left x B) H_object_at_node)))) with 
                (((projT1 (projT2 (nodal_multi_bracket_left (x:= x) H_object_at_node)))) /\1 unitt B).
                     **)
                     **)

                    intros z [J1 | [J1 | J1]].
                    + rewrite J1. auto.
                    + { 
                        Lemma lem032 A (x y : nodes A) : (lt_left_eq x y) + (lt_left_eq x y -> Empty_set).
                          assert (H_dec : (eq x y) + ((lt_left x y + (lt_right x y + lt_par x y)) + (lt_left y x + (lt_right y x + lt_par y x))) ) by auto.
                          destruct H_dec as [H_dec | [[H_dec | H_dec] | H_dec]];
                            [ auto | auto 
                              | right; revert H_dec; intros [H_dec | H_dec] [K1 | K1]; repeat (dependent induction H_dec; dependent destruction K1; auto) 
                              | right; revert H_dec; intros [H_dec | [H_dec | H_dec]] [K1 | K1]; repeat (dependent induction H_dec; dependent destruction K1; auto)]. 
                        Defined.
                        Hint Resolve lem032.

                        destruct (lem032 (f x) z) as [J2 | J2].
                        - elimtype Empty_set. destruct J2 as [J2 | J2].
                          subst z. apply (lem007300 (inl J1)); auto (*from 2-assumption H_lt_right_once_fx_fy'_rewrite*).
                          assert (J3 : lt_left (f' (f x)) (f' z)) by auto.
                          assert (J4 :  lt_right (f' (f x)) (f' z)) by
                              (apply (lem00710' (y:= (f' (f y')) )); auto).
                          apply  (lem007400 J3 J4).
                        - right; left.
                          apply H_cumul_lt_left_M.
                          + replace ( (rev f') (f' z)  ) with ( z ) by auto.
                            assumption (*exact J2*).
                          + assumption (*exact J1*).
                      }
                    + right; right.
                      replace ( (rev f') (f' (f y')) ) with ( f y' ) by auto.
                      replace ( (rev f') (f' z)  ) with ( z ) by auto.
                      eauto (*apply (lem033 f'); exact J1*).
                  }
              }
              (**com_assoc f f'**)
              apply lem068; assumption.                    
            }

            (**STEP**)
            assert (H_object_at_node_fy'_all : forall t (H_lt_leftorright_eq_fy'_t : lt_leftorright_eq (f y') t), object_at_node t = object_at_node (f' t)).
            {
              intros.
              assert (H_lt_right_fx_t : lt_right (f x) t) by (eapply lem00710'; eassumption).
              rewrite (H_eq_f'y' _ H_lt_right_fx_t).
              rewrite <- (fun H x => objects_eq_same (objects_same_term_arrow_post1 H x)).
              simpl.

              Lemma lem015 (A B C : objects) (Dlist : list objects) 
              : forall (z : nodes B), object_at_node ( (multi_bracket_left A B C Dlist) ( at_right A ( foldrightn (at_left z C) Dlist ) ) ) = object_at_node z .
              
                induction Dlist as [ | E Dlist].
                - compute. auto.
                - unfold multi_bracket_left (*autounfold*). autorewrite * with core using eauto (*rewrite lem081*).
              Defined. Hint Resolve lem015. Hint Rewrite lem015 using eauto.

              Lemma lem014 A B C Dlist (z : nodes (A /\ ((B /\ C) /\\ Dlist))) (H_lt_leftorright_eq_self_z : lt_leftorright_eq ( at_right A ( foldrightn (at_left (self B) C) Dlist ) ) z )
              : object_at_node ( (multi_bracket_left A B C Dlist) ( z ) ) = object_at_node z.

                destruct H_lt_leftorright_eq_self_z as [H_lt_leftorright_eq_self_z | [H_lt_leftorright_eq_self_z | H_lt_leftorright_eq_self_z]].
                - replace z. rewrite lem064. (*symmetry; auto = *) clear z H_lt_leftorright_eq_self_z; induction Dlist; simpl; auto.
                - replace (z) with ( loc_rev _ (loc' H_lt_leftorright_eq_self_z) ) by auto.

                  Lemma lem013 A (x : nodes A) (y : object_at_node x) : object_at_node (loc_rev x y) = object_at_node y.
                    induction x.
                    - simpl. reflexivity.
                    - simpl in *. apply IHx.
                    - simpl in *. apply IHx.
                  Defined. Hint Resolve lem013. Hint Rewrite lem013 using eauto.
                  Lemma lem012 A (x : nodes A) B (H : A = B) : object_at_node (eq_rect _ nodes x _ H ) = object_at_node x.
                    destruct H; reflexivity.                  
                  Defined. Hint Resolve lem012. Hint Rewrite lem012 using eauto.

                  (**/!\NO PROGRESS: autorewrite * with core using auto. ?? Setoid Rewrite ??**)
                  rewrite lem013. rewrite lem020. rewrite lem015. rewrite lem012. reflexivity.
                - replace (z) with ( loc_rev _ (loc H_lt_leftorright_eq_self_z) ) by auto.
                  rewrite lem013. rewrite lem020. rewrite lem015. rewrite lem012. reflexivity.
              Defined. Hint Resolve lem014. Hint Rewrite lem014 using eauto.

              rewrite lem014.
              - { Lemma lem011 A A' (H_objects_same : objects_same A A') (x : nodes A') 
                  : object_at_node ((lem071 H_objects_same) x) = object_at_node x.
              
                    induction H_objects_same.
                    - simpl. reflexivity.
                    - simpl. dependent destruction x. 
                      + simpl. rewrite (objects_eq_same H_objects_same1); rewrite (objects_eq_same H_objects_same2). reflexivity. 
                      + apply IHH_objects_same1.
                      + apply IHH_objects_same2.
                  Defined. Hint Resolve lem011. Hint Rewrite lem011 using eauto.

                  rewrite lem011.
                  rewrite lem121. reflexivity.
                }
              - rewrite lem072. Print Implicit lem061.
                (**/!\BUG COQ no progress : replace (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr)))) with (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_right_fx_fy')) by (eapply lem061; eexact H_list_E2_nodes). **)
                assert (Htemp := lem061 _ _ H_list_E2_nodes). simpl in Htemp |- *. rewrite <- Htemp. clear Htemp.
                SearchPattern (lt_leftorright_eq (nodes_map _ _) _).
                SearchPattern (lt_leftorright_eq _ _).
                
                Lemma lem010 A A' (H_objects_same : objects_same A A') (x y : nodes A) (H_lt_leftorright_eq_x_y : lt_leftorright_eq x y) : lt_leftorright_eq (nodes_map H_objects_same x) (nodes_map H_objects_same y).
                  induction H_objects_same.
                  - simpl.  assumption.
                  - dependent destruction x; dependent destruction y; destruct H_lt_leftorright_eq_x_y as [H_lt_leftorright_eq_x_y | [H_lt_leftorright_eq_x_y | H_lt_leftorright_eq_x_y]]; dependent destruction H_lt_leftorright_eq_x_y; simpl in *; auto. (** :) 1 ATTEMPT only **)
                Defined. Hint Resolve lem010.

                auto (**apply lem010; apply lem027; assumption**).
            }

            (**STEP**)
            assert (H_object_at_node_fy_all : forall t (H_lt_leftorright_eq_fy_t : lt_leftorright_eq (f y) t), object_at_node t = object_at_node (f' t)).
            {
              intros.
              assert (H_lt_left_fx_fy : lt_left (f x) (f y)) by auto.
              assert (H_lt_left_fx_t : lt_left (f x) t) by (eapply lem00710''; eassumption).
              rewrite (H_eq_f'y _ H_lt_left_fx_t).
              rewrite <- (fun H x => objects_eq_same (objects_same_term_arrow_post1 H x)).
              simpl.
              rewrite lem072.

              Lemma lem009 (A B C : objects) (Dlist : list objects) 
              : forall (z : nodes A), object_at_node ( (multi_bracket_left A B C Dlist) ( at_left z ((B/\C)/\\Dlist) ) ) = object_at_node z .
              
                induction Dlist as [ | E Dlist].
                - compute. auto.
                - unfold multi_bracket_left (*autounfold*). autorewrite * with core using eauto (*rewrite lem081*).
              Defined. Hint Resolve lem009. Hint Rewrite lem009 using eauto.

              Lemma lem008 A B C Dlist (z : nodes (A /\ ((B /\ C) /\\ Dlist))) (H_lt_leftorright_eq_self_z : lt_leftorright_eq ( at_left (self A) ( (B/\C)/\\Dlist ) ) z )
              : object_at_node ( (multi_bracket_left A B C Dlist) ( z ) ) = object_at_node z.

                destruct H_lt_leftorright_eq_self_z as [H_lt_leftorright_eq_self_z | [H_lt_leftorright_eq_self_z | H_lt_leftorright_eq_self_z]].
                - replace z. SearchRewrite (object_at_node (_ (_) (at_left _ _))) (*apply lem019 = *). autorewrite * with core using auto.
                - replace (z) with ( loc_rev _ (loc' H_lt_leftorright_eq_self_z) ) by auto.
                  (**/!\NO PROGRESS: autorewrite * with core using auto. ?? Setoid Rewrite ??**)
                  rewrite lem013. SearchRewrite (loc_rev (at_left _ _) _).
                  rewrite lem016.
                  apply lem009.
                - replace (z) with ( loc_rev _ (loc H_lt_leftorright_eq_self_z) ) by auto.
                  rewrite lem013. rewrite lem016. apply lem009. 
              Defined. Hint Resolve lem008. Hint Rewrite lem008.

              rewrite lem008.
              - rewrite <- lem072.
                rewrite lem011. SearchRewrite (object_at_node (loc _)). (*return lem121*)
                SearchRewrite (object_at_node (loc' _)) (*return nothing*).
                Lemma lem007 (A : objects) (x : nodes A) (y : nodes A) (H_lt_left_x_y : lt_left x y) : object_at_node (loc' H_lt_left_x_y) = object_at_node y.

                  induction H_lt_left_x_y; simpl; auto. (* :D 1 attempt only :) *)
                Defined.
                Hint Resolve lem007.
                Hint Rewrite lem007 using auto.
                
                rewrite lem007. reflexivity.
              - assert (lt_left_once (self _) (loc' H_lt_left_fx_fy)) by auto.
                assert (lt_left_once (self _) ((nodes_map (objects_same_sym H_same_object_at_node) (loc' H_lt_left_fx_fy)))) by (rewrite <- (lem091  (objects_same_sym H_same_object_at_node)); auto).

                (**/!\BUG Fail rewrite (lem065 H0). (**NONO 7000 lines Set Printing All. Show.**) **)
                assert (Htemp1 := (lem065 H0)).
                simpl in Htemp1. rewrite <- Htemp1. clear Htemp1.
                
                (*auto. = *) apply lem010. SearchPattern (lt_leftorright_eq (loc' _) (loc' _)). apply lem021; assumption.
            }

            
            (**STEP**)
            assert (H_node_is_lettery_fy'_all : forall t (H_lt_leftorright_eq_fy'_t : lt_leftorright_eq (f y') t), node_is_lettery f' t).
            {
              assert (H_node_is_lettery_fy'_all_half : forall t (H_lt_leftorright_eq_fy'_t : lt_leftorright_eq (f y') t), (forall x0 : A, lt_leftorright_eq t x0 -> lt_leftorright_eq (f' t) (f' x0))).
              { intros ? ? .
                assert (H_lt_right_fx_t : lt_right (f x) t) by (eapply lem00710'; eassumption).
                rewrite (H_eq_f'y' _ H_lt_right_fx_t).
                intros z J1.
                assert (J2 : lt_right (f x) z) by (eapply lem00710'; eassumption).
                rewrite (H_eq_f'y' _ J2).
                SearchPattern (lt_leftorright_eq (cat_term_arrow_on_nodes_target _ _) _). (*return lem047*)
                apply lem047.
                simpl.
                apply lem057_post2.
                * (**/!\BUG fail erewrite <- (lem061 _ _ H_list_E2_nodes).**)
                  (**lem061 :  nodes_map (objects_same_sym H_objects_same) x' = x.**)
                  assert (Htemp := (lem061 _ _ H_list_E2_nodes)); simpl in Htemp |- *; rewrite <- Htemp; clear Htemp.
                  (** lem072 : (lem071 H_objects_same) x = nodes_map (objects_same_sym H_objects_same) x. **)
                  rewrite lem072.
                  auto.
                * auto. 
              }

              intros.
              assert (H_lt_right_fx_t : lt_right (f x) t) by (eapply lem00710'; eassumption).

              split.
              - apply H_node_is_lettery_fy'_all_half; assumption.
              - assert (H_lt_leftorright_eq_fy'_t_rewrite : lt_leftorright_eq (f' (f y')) (f' t)) by (eapply H_node_is_lettery_fy'_all_half; auto).
                intros z [J1 | [J1 | J1]].
                + rewrite J1. auto.
                + 
                  (* Lemma lem032 A (x y : nodes A) : (lt_left_eq x y) + (lt_left_eq x y -> Empty_set). *)
                  { destruct (lem032 (f x) z) as [J2 | J2].
                    - elimtype Empty_set. destruct J2 as [J2 | J2].
                      * subst z. apply (lem007300 (inl J1)).
                        (**/!\OLD GENERATE EVAR EXITENTIAL GOAL FOR LATER, NEW SOLVE THE GOAL AT ONCE
                            right; eapply (lem00710' _ H_lt_leftorright_eq_fy'_t_rewrite). **)
                        right; cut (lt_right (f' (f x)) (f' (f y')));[
                          intros Htemp; eapply (lem00710' Htemp H_lt_leftorright_eq_fy'_t_rewrite); clear Htemp
                        | auto ].
                      * assert (J3 : lt_left (f' (f x)) (f' z)) by auto.
                        assert (J4 :  lt_right (f' (f x)) (f' z)) by
                            (eapply (lem00710' (y:= (f' t))); [
                               eapply (lem00710' (y:= (f' (f y')))); auto |  auto ]).
                        apply  (lem007400 J3 J4).
                    - right; left.
                      apply H_cumul_lt_left_M.
                      + replace ( (rev f') (f' z)  ) with ( z ) by auto.
                        assumption (*exact J2*).
                      + assumption (*exact J1*).
                  }
                + right; right.
                  replace ( (rev f') (f' t) ) with ( t ) by auto.
                  replace ( (rev f') (f' z)  ) with ( z ) by auto.
                  eauto (*apply (lem033 f'); exact J1*).
            }

            (**STEP**)
            assert (H_node_is_lettery_y_full : node_is_lettery (com_assoc f f') y).
            { 
              assert (H_node_is_lettery_fy : node_is_lettery f' (f y)).
              {
                split.
                - (**begin same as proof of  assert (H_object_at_node_fy : object_at_node (f y) = object_at_node (f' (f y))). **)            
                  assert (H_lt_left_fx_fy : lt_left (f x) (f y)) by auto.
                  rewrite (H_eq_f'y _ H_lt_left_fx_fy).
                  intros z J1.
                  assert (J2 : lt_left (f x) z) by (eapply lem00710''; eassumption).
                  rewrite (H_eq_f'y _ J2).
                  apply lem047.
                  simpl arrows_assoc_on_nodes.
                  rewrite ?lem072 (** only first rewrite occurence is lacked, the extra rewrite will be reversed below**).

                  assert (K1 : lt_left_once (self _) (loc' H_lt_left_fx_fy)) by auto.
                  assert (K2 : lt_left_once (self _) ((nodes_map (objects_same_sym H_same_object_at_node) (loc' H_lt_left_fx_fy)))) by (rewrite <- (lem091  (objects_same_sym H_same_object_at_node)); auto).
                  assert (Htemp1 := (lem065 K2)).
                  simpl in Htemp1. rewrite Htemp1. clear Htemp1.
                  simpl.

                  apply lem055.
                  (**/!\BUG COQ will fail or not progress at alone [rewrite <- (lem065 K2)] without first both [simpl in K2] and [simpl] **)
                  simpl in K2. simpl. rewrite <- (lem065 K2).
                  rewrite <- ?lem072.
                  cut ( lt_leftorright_eq (loc' H_lt_left_fx_fy) (loc' J2) ); 
                    [ auto (*intros Htemp; apply lem048; exact Htemp*)
                    | auto (*apply lem049; assumption*) ].
                - intros z [J1 | [J1 | J1]].
                  + rewrite J1. auto.
                  + destruct (lem032 (f x) z) as [J2 | J2].
                    * { destruct J2 as [J2 | J2].
                        - elimtype Empty_set. subst z. apply (lem007300 (inl J1)).
                          cut (lt_left (f' (f x)) (f' (f y))) ; [
                              auto
                            | cut (lt_left (f x) (f y)) ; [
                                auto (*apply lem034*)
                              | auto ] 
                            ].
                        - replace ( (rev f') (f' (f y)) ) with ( f y ) by auto.
                          replace ( (rev f') (f' z)  ) with ( z ) by auto.
                          SearchAbout (  lt_left_once _ _ -> lt_leftorright_eq _ _). (*returns nothing*)
                          SearchAbout (  lt_left_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010500*)
                          apply (lem010500 H_lt_left_once_fx_fy J2).
                      }
                    * { right; left.
                        apply H_cumul_lt_left_M.
                        + replace ( (rev f') (f' z)  ) with ( z ) by auto.
                          assumption (*exact J2*).
                        + assumption (*exact J1*).
                      }
                  + right; right.
                    replace ( (rev f') (f' (f y)) ) with ( f y ) by auto.
                    replace ( (rev f') (f' z)  ) with ( z ) by auto.
                    apply (lem033 f'); exact J1.
              (* eauto (*apply (lem033 f'); exact J1*).*)
              }

              (**com_assoc f' f**)
              apply lem068; assumption.
            }

            assert (H_node_is_lettery_fy_all : forall t (H_lt_leftorright_eq_fy'_t : lt_leftorright_eq (f y) t), node_is_lettery f' t).
            {
              intros. assert (H_lt_left_fx_t : lt_left (f x) t) by (cut (lt_left (f x) (f y)); [ intros Htemp; eapply (lem00710'' Htemp H_lt_leftorright_eq_fy'_t); assumption | auto ]).
              split.
              - rewrite (H_eq_f'y _ H_lt_left_fx_t).
                intros z J1.
                assert (J2 : lt_left (f x) z) by (cut (lt_left (f x) t); [ intros Htemp; eapply (lem00710'' Htemp J1); eassumption | auto ]).
                rewrite (H_eq_f'y _ J2).
                SearchPattern (lt_leftorright_eq (cat_term_arrow_on_nodes_target _ _) _). (*return lem047*)
                apply lem047.
                simpl.
                apply lem055_post2.
                * (* lem072 : (lem071 H_objects_same) x = nodes_map (objects_same_sym H_objects_same) x*)
                  rewrite lem072.
                  assert (H_lt_left_fx_fy : lt_left (f x) (f y)) by auto.
                  assert (K1 : lt_left_once (self _) (loc' H_lt_left_fx_fy)) by auto.
                  assert (K2 : lt_left_once (self _) ((nodes_map (objects_same_sym H_same_object_at_node) (loc' H_lt_left_fx_fy)))) by (rewrite <- (lem091  (objects_same_sym H_same_object_at_node)); auto).
                  assert (Htemp1 := (lem065 K2)).
                  simpl in Htemp1. rewrite <- Htemp1. clear Htemp1.
                  auto.
                * auto.
              - intros z [J1 | [J1 | J1]].
                + rewrite J1. auto.
                + destruct (lem032 (f x) z) as [J2 | J2].
                  * { destruct J2 as [J2 | J2].
                      - elimtype Empty_set. subst z. apply (lem007300 (inl J1)).
                        cut (lt_left (f' (f x)) (f' t)) ; [
                            auto
                          | cut (lt_left (f x) t) ; [
                              auto (*apply lem034*)
                            |  assumption ] 
                          ].
                      - (*replace ( (rev f') (f' t) ) with ( t ) by auto.
                            replace ( (rev f') (f' z)  ) with ( z ) by auto.*)
                        rewrite (H_eq_f'y _ H_lt_left_fx_t) in J1.
                        rewrite (H_eq_f'y _ J2) in J1.
                        Check lem047.
                        SearchAbout (lt_leftorright_eq (cat_term_arrow_on_nodes_target _ _) _). (*return lem047*)
                        Lemma lem006 A' B' (f' : arrows A' B') A B (f : arrows A B) (H_term_arrow_f'_f : term_arrow f' f) (y z : nodes B') (H_lt_leftorright_eq_y_z : lt_leftorright_eq (H_term_arrow_f'_f y) (H_term_arrow_f'_f z)) : lt_leftorright_eq y z.
                          induction H_term_arrow_f'_f.
                          - simpl in *; assumption.
                          - simpl in *. apply IHH_term_arrow_f'_f.
                            destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]]; dependent destruction H_lt_leftorright_eq_y_z; auto.
                          - simpl in *. apply IHH_term_arrow_f'_f.
                            destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]]; dependent destruction H_lt_leftorright_eq_y_z; auto.
                        Defined.
                        Hint Resolve lem006.
                        Show. Print inl.
                        assert (J3 : lt_leftorright_eq
                                       ( ((lem070
                                             (multi_bracket_left E1
                                                                 (object_at_node (loc H_lt_right_fx_fy')) 
                                                                 (projT1 mfr) (projT1 (projT2 mfr))) H_same_object_at_node)
                                            (loc' H_lt_left_fx_t)))
                                       ( ((lem070
                                             (multi_bracket_left E1
                                                                 (object_at_node (loc H_lt_right_fx_fy')) 
                                                                 (projT1 mfr) (projT1 (projT2 mfr))) H_same_object_at_node)
                                            (loc' J2))) ).
                        apply (lem006 H_term_arrow_f'). auto.
                        
                        clear J1.
                        simpl in J3.
                        assert ( lt_leftorright_eq
                                   (( ((lem071 H_same_object_at_node) (loc' H_lt_left_fx_t))))
                                   (( ((lem071 H_same_object_at_node) (loc' J2)))) ). 
                        cut (lt_leftorright_eq (at_left (self E1) (((object_at_node (loc H_lt_right_fx_fy')) /\ (projT1 mfr)) /\\ (projT1 (projT2 mfr)) ))  ((lem071 H_same_object_at_node) (loc' H_lt_left_fx_t))).
                        intros K1.
                        destruct (@lem055_post2 E1 (object_at_node (loc H_lt_right_fx_fy')) (projT1 mfr) (projT1 (projT2 mfr)) ((lem071 H_same_object_at_node) (loc' H_lt_left_fx_t)) K1) as (L1 & L2).
                        simpl in *.
                        replace ( ((rev
                                (projT1
                                   (multi_bracket_left_specif E1
                                                              (object_at_node (loc H_lt_right_fx_fy')) 
                                                              (projT1 mfr) (projT1 (projT2 mfr)))))
                               ((projT1
                                   (multi_bracket_left_specif E1
                                                              (object_at_node (loc H_lt_right_fx_fy')) 
                                                              (projT1 mfr) (projT1 (projT2 mfr))))
                                  ((lem071 H_same_object_at_node) (loc' H_lt_left_fx_t)))) ) 
                        with ((lem071 H_same_object_at_node) (loc' H_lt_left_fx_t)) in L2 by auto.
                        assert ( L2' : forall x0 : up_0 E1
                                                        ((object_at_node (loc H_lt_right_fx_fy') /\ projT1 mfr) /\\
                                                                                                                projT1 (projT2 mfr)),
                                         lt_leftorright_eq
                                           ((projT1
                                               (multi_bracket_left_specif E1
                                                                          (object_at_node (loc H_lt_right_fx_fy')) 
                                                                          (projT1 mfr) (projT1 (projT2 mfr))))
                                              ((lem071 H_same_object_at_node) (loc' H_lt_left_fx_t)))
                                           ((projT1
                                               (multi_bracket_left_specif E1
                                                                          (object_at_node (loc H_lt_right_fx_fy')) 
                                                                          (projT1 mfr) (projT1 (projT2 mfr)))) x0) ->
                                         lt_leftorright_eq
                                           ((lem071 H_same_object_at_node) (loc' H_lt_left_fx_t))
                                           x0 ).
                        intros x0 ? .
                        replace x0  with ((rev
                                             (projT1
                                                (multi_bracket_left_specif E1
                                                                           (object_at_node (loc H_lt_right_fx_fy')) 
                                                                           (projT1 mfr) (projT1 (projT2 mfr)))))
                                            ((projT1
                                                (multi_bracket_left_specif E1
                                                                           (object_at_node (loc H_lt_right_fx_fy')) 
                                                                           (projT1 mfr) (projT1 (projT2 mfr)))) x0))
                          by auto.
                        apply L2. assumption.
                        apply L2'.                           
                        exact J3.
                        (* lem072 : (lem071 H_objects_same) x = nodes_map (objects_same_sym H_objects_same) x*)
                        rewrite lem072.
                        assert (H_lt_left_fx_fy : lt_left (f x) (f y)) by auto.
                        assert (K1 : lt_left_once (self _) (loc' H_lt_left_fx_fy)) by auto.
                        assert (K2 : lt_left_once (self _) ((nodes_map (objects_same_sym H_same_object_at_node) (loc' H_lt_left_fx_fy)))) by (rewrite <- (lem091  (objects_same_sym H_same_object_at_node)); auto).
                        assert (Htemp1 := (lem065 K2)).
                        simpl in Htemp1 |- *. rewrite <- Htemp1. clear Htemp1.
                        auto.

                        replace ( (rev f') (f' t) ) with ( t ) by auto.
                        replace ( (rev f') (f' z)  ) with ( z ) by auto.
                        SearchPattern (lt_leftorright_eq _ _).
                        Lemma lem005
                              (A0 A1 : objects) (H_objects_same : objects_same A0 A1) (y z : A1)
                              (H_lt_leftorright_eq_y_z : lt_leftorright_eq ((lem071 H_objects_same) y) ((lem071 H_objects_same) z))
                        :   lt_leftorright_eq y z.
                          induction H_objects_same.
                          - simpl; assumption.
                          - dependent destruction y; dependent destruction z;
                            destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]];
                            dependent destruction H_lt_leftorright_eq_y_z;
                            simpl in *; auto. (** :D 1 attempt only FYEAH ! :) **)
                        Defined. Hint Resolve lem005.
                        SearchPattern (lt_leftorright_eq _ _). (**TO ERASE lem049 is DUPLICATE of lem021**)

                        Lemma lem004
                              (A : objects) (x y : A) (H_lt_left_x_y : lt_left x y) 
                        : forall  (z : A) (H_lt_left_x_z : lt_left x z)
                                  (H_lt_leftorright_eq_y_z : lt_leftorright_eq (loc' H_lt_left_x_y) (loc' H_lt_left_x_z))
                          , lt_leftorright_eq y z.

                          induction H_lt_left_x_y;   dependent destruction H_lt_left_x_z.
                          - simpl. tauto.
                          - simpl in *. intros. cut (lt_leftorright_eq y y0); eauto.
                          - simpl in *. intros. cut (lt_leftorright_eq y y0); eauto. 
                        Defined. Hint Resolve lem004.
                        Show.
                        assert (lt_leftorright_eq
                                  ((loc' H_lt_left_fx_t))
                                  ((loc' J2))). apply (lem005 H_same_object_at_node). assumption.

                        revert H0. apply lem004.
                    }
                  * { right; left.
                      apply H_cumul_lt_left_M.
                      + replace ( (rev f') (f' z)  ) with ( z ) by auto.
                        assumption (*exact J2*).
                      + assumption (*exact J1*).
                    }
                + right; right.
                  replace ( (rev f') (f' t) ) with ( t ) by auto.
                  replace ( (rev f') (f' z)  ) with ( z ) by auto.
                  eauto (*apply (lem033 f'); exact J1*).
            }
            (**?? LOOK FOR ALTERNATIVE TO PROOF OF  H_node_is_lettery_fy'_all H_node_is_lettery_fy_all WHICH USES LEMMA LEM048 INSTEAD ??**)

            (**STEP**)
            assert (H_lt_left_once_fx_fy_rewrite : lt_left_once (f' (f x)) (f' (f y))). 
            { (*lem053*)
              rewrite (H_eq_f'x).
              assert (H_lt_left_fx_fy : lt_left (f x) (f y)) by auto.
              rewrite (H_eq_f'y _ H_lt_left_fx_fy).
                 
              Lemma lem031 A' B' (f' : arrows A' B') A B (f : arrows A B) (H_term_arrow_f'_f : term_arrow f' f) (y z : nodes B') (H_lt_leftorright_eq_y_z : lt_left_once y z) : lt_left_once (H_term_arrow_f'_f y) (H_term_arrow_f'_f z).

                induction H_term_arrow_f'_f;
                simpl in *; auto.
              Defined.
              Hint Resolve lem031.

              apply lem031.
              simpl arrows_assoc_on_nodes.
              SearchPattern ( (lem071 _) (self _) = (self _)). (*returns lem071_post2*)
              (** rewrite lem071. (**/!\ interesting error: [build_signature: no constraint can apply on a dependent argument] *)*)
              rewrite lem071_post2.
              rewrite lem072.
              assert (K1 : lt_left_once (self _) (loc' H_lt_left_fx_fy)) by auto.
              assert (K2 : lt_left_once (self _) ((nodes_map (objects_same_sym H_same_object_at_node) (loc' H_lt_left_fx_fy)))) by (rewrite <- (lem091  (objects_same_sym H_same_object_at_node)); auto).
              assert (Htemp1 := (lem065 K2)).
              simpl in Htemp1. rewrite Htemp1. clear Htemp1.
              
              apply lem053 (**/!\ Fail progress auto**).
            }

            (**STEP**)
            assert (H_node_is_lettery_x : node_is_lettery (com_assoc f f') x) 
              by (apply (lem010800 (com_assoc f f') H_lt_left_once_x_y  H_lt_left_once_fx_fy_rewrite H_lt_right_once_x_y'); assumption).

            (**STEP**)
            assert (H_node_is_lettery_x_all_full : forall t : nodes B, lt_leftorright_eq x t -> node_is_lettery (com_assoc f f') t).
            {
              intros t [H_lt_leftorright_eq_x_t | [H_lt_leftorright_eq_x_t | H_lt_leftorright_eq_x_t]].
              - subst t. exact H_node_is_lettery_x.
              - SearchAbout (  lt_left_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010500*)
                assert (H_lt_leftorright_eq_y_t : lt_leftorright_eq y t) by ( apply (lem010500 H_lt_left_once_x_y H_lt_leftorright_eq_x_t)).
                assert (H_cumul_letteries_t_true : cumul_letteries t = true) by (eapply (H_cumul_letteries_satur _ H_cumul_letteries_y_true); eassumption).
                apply lem068.
                + exact (H_node_is_lettery _ H_cumul_letteries_t_true). 
                + apply H_node_is_lettery_fy_all. apply H_node_is_lettery_y; assumption.
              - SearchAbout (  lt_right_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010600*)
                assert (H_lt_leftorright_eq_y'_t : lt_leftorright_eq y' t) by ( apply (lem010600 H_lt_right_once_x_y' H_lt_leftorright_eq_x_t)).
                assert (H_cumul_letteries_t_true : cumul_letteries t = true) by (eapply (H_cumul_letteries_satur _ H_cumul_letteries_y'_true); eassumption).
                apply lem068.
                + exact (H_node_is_lettery _ H_cumul_letteries_t_true). 
                + apply H_node_is_lettery_fy'_all. apply H_node_is_lettery_y'; assumption.
            }

            (**STEP**)
            assert (H_object_at_node_x : object_at_node x = object_at_node ((com_assoc f f') x))
              by (simpl; apply (lem011000 (com_assoc f f') H_lt_left_once_x_y  H_lt_left_once_fx_fy_rewrite H_lt_right_once_x_y'); assumption).

            (**STEP**)
            assert (H_object_at_node_x_all_full : forall t : nodes B, lt_leftorright_eq x t ->  object_at_node t = object_at_node ((com_assoc f f') t)).
            {
              intros t [H_lt_leftorright_eq_x_t | [H_lt_leftorright_eq_x_t | H_lt_leftorright_eq_x_t]].
              - subst t. exact H_object_at_node_x.
              - SearchAbout (  lt_left_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010500*)
                assert (H_lt_leftorright_eq_y_t : lt_leftorright_eq y t) by ( apply (lem010500 H_lt_left_once_x_y H_lt_leftorright_eq_x_t)).
                assert (H_cumul_letteries_t_true : cumul_letteries t = true) by (eapply (H_cumul_letteries_satur _ H_cumul_letteries_y_true); eassumption). Check lem011000.
                simpl.
                transitivity (object_at_node ( f t  ) ).
                + exact (H_object_at_node _  H_cumul_letteries_t_true). 
                + apply H_object_at_node_fy_all. apply H_node_is_lettery_y; assumption.
              - SearchAbout (  lt_right_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010600*)
                assert (H_lt_leftorright_eq_y'_t : lt_leftorright_eq y' t) by ( apply (lem010600 H_lt_right_once_x_y' H_lt_leftorright_eq_x_t)).
                assert (H_cumul_letteries_t_true : cumul_letteries t = true) by (eapply (H_cumul_letteries_satur _ H_cumul_letteries_y'_true); eassumption).
                simpl.
                transitivity (object_at_node ( f t  ) ).
                + exact (H_object_at_node _  H_cumul_letteries_t_true). 
                + apply H_object_at_node_fy'_all. apply H_node_is_lettery_y'; assumption.
            }

            set (more_cumul_letteries cumul_letteries H_cumul_letteries_wellform H_cumul_letteries_x_false) as H_more_cumul_letteries.
            set (projT1 H_more_cumul_letteries) as H_more_cumul_letteries_1.
            set (projT1(projT2 H_more_cumul_letteries)) as H_more_cumul_letteries_2.
            set (projT2(projT2 H_more_cumul_letteries)) as H_more_cumul_letteries_3.
            hnf in (type of H_more_cumul_letteries_3).
            fold H_more_cumul_letteries_2 in H_more_cumul_letteries_3.
            fold H_more_cumul_letteries_1 in H_more_cumul_letteries_2, H_more_cumul_letteries_3.

            (**STEP**)
            assert (H_more_cumul_letteries_4 : lengthn'' H_more_cumul_letteries_1 H_more_cumul_letteries_2 <= S len) by auto with zarith (*/!\note that without those two [fold] above this alt proof only : ((*/!\careful with this non-clean proof/!\*) subst H_more_cumul_letteries_1; subst H_more_cumul_letteries_2; auto with zarith) *).

            (**STEP**)
            assert (H_more_cumul_letteries_5_satur : forall y : nodes B, H_more_cumul_letteries_1 y = true -> forall z : nodes B, lt_leftorright_eq y z ->  H_more_cumul_letteries_1 z = true).
            {
              intros t. unfold H_more_cumul_letteries_1. unfold projT1. unfold H_more_cumul_letteries.
              unfold more_cumul_letteries.
              destruct (nodes_eq_dec t x) as [Heq_t_x | Heq_t_x].
              + subst t. intros _ t [H_lt_leftorright_eq_x_t | [H_lt_leftorright_eq_x_t | H_lt_leftorright_eq_x_t]].
              - subst t. SearchRewrite (nodes_eq_dec _ _) (*nothing*). 
                destruct (nodes_eq_dec x x) as [J1 | J1]; [reflexivity | exfalso; apply J1; reflexivity].
              - destruct (nodes_eq_dec t x) as [J1 | J1]; [elimtype Empty_set; apply (lem007100 J1); auto | idtac].
                SearchAbout (  lt_left_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010500*)
                assert (H_lt_leftorright_eq_y_t : lt_leftorright_eq y t) by ( apply (lem010500 H_lt_left_once_x_y H_lt_leftorright_eq_x_t)).
                assert (H_cumul_letteries_t_true : cumul_letteries t = true) by (eapply (H_cumul_letteries_satur _ H_cumul_letteries_y_true); eassumption).
                exact H_cumul_letteries_t_true.
              - destruct (nodes_eq_dec t x) as [J1 | J1]; [elimtype Empty_set; apply (lem007100 J1); auto | idtac].
                SearchAbout (  lt_right_once _ _ -> _ -> _  -> lt_leftorright_eq _ _). (*returns lem010600*)
                assert (H_lt_leftorright_eq_y'_t : lt_leftorright_eq y' t) by ( apply (lem010600 H_lt_right_once_x_y' H_lt_leftorright_eq_x_t)).
                assert (H_cumul_letteries_t_true : cumul_letteries t = true) by (eapply (H_cumul_letteries_satur _ H_cumul_letteries_y'_true); eassumption).
                exact H_cumul_letteries_t_true.
                + intros J1 z J2. destruct (nodes_eq_dec z x) as [J3 | J3]; [reflexivity | idtac].
                  apply (H_cumul_letteries_satur t); assumption.
            }

            (**STEP**)
            assert (H_node_is_lettery_more: forall x : B,
                                              H_more_cumul_letteries_1 x = true -> node_is_lettery (com_assoc f f') x).
            {
              intros t. unfold H_more_cumul_letteries_1. unfold projT1. unfold H_more_cumul_letteries.
              unfold more_cumul_letteries.
              (*lem006800:
  forall (A : objects) (x y : A),
  (x = y) +
  (lt_left x y + (lt_right x y + lt_par x y) +
   (lt_left y x + (lt_right y x + lt_par y x)))*)              
              Lemma lem003 A (x y : nodes A) : lt_leftorright_eq x y + (lt_leftorright_eq x y -> Empty_set).
                assert (H_dec : (eq x y) + ((lt_left x y + (lt_right x y + lt_par x y)) + (lt_left y x + (lt_right y x + lt_par y x))) ) by auto.
                destruct H_dec as [H_dec | [[H_dec | [H_dec | H_dec]] | H_dec]];
                  [ tauto | tauto | tauto 
                    | right; revert H_dec; intros H_dec [K1 | [K1 | K1]]; repeat (dependent induction H_dec; dependent destruction K1; auto) 
                    | right; revert H_dec; intros [H_dec | [H_dec | H_dec]] [K1 | [K1 | K1]]; repeat (dependent induction H_dec; dependent destruction K1; auto)]. (** :D 1 ATTEMPT ONLY FYEAH **)
              Defined.
              Hint Resolve lem003.

              destruct (lem003 x t) as [H_lt_leftorright_eq_x_t | H_no_lt_leftorright_eq_x_t].
              + intros _. apply H_node_is_lettery_x_all_full. assumption.
              + { (*assert (H_no_lt_leftorright_eq_fx_ft : lt_leftorright_eq (f x) (f t) -> Empty_set)
                  by (intros; apply H_no_lt_leftorright_eq_x_t;
                      replace t with ((rev f) (f t)) by auto;
                      replace x with ((rev f) (f x)) by auto; apply H_node_is_lettery_x; assumption).*)

                  Lemma lem002 A (x y : nodes A) (H_no_lt_leftorright_eq_x_y : lt_leftorright_eq x y -> Empty_set) (H_no_lt_leftorright_eq_y_x : lt_leftorright_eq y x -> Empty_set) : lt_par_or x y.
                    assert (H_dec : (eq x y) + (lt_par_or x y + lt_leftorright_or x y)) by auto.
                    destruct H_dec as [H_dec | [H_dec | [H_dec | H_dec]]];
                      [ elimtype Empty_set; apply H_no_lt_leftorright_eq_x_y; tauto
                      | assumption
                      | elimtype Empty_set; apply H_no_lt_leftorright_eq_x_y; tauto
                      | elimtype Empty_set; apply H_no_lt_leftorright_eq_y_x; tauto ]. (** :D 1 ATTEMPT ONLY FYEAH **)
                  Defined. Hint Resolve lem002.

                  destruct (nodes_eq_dec t x) as [Heq_t_x | Heq_no_t_x]; [elimtype Empty_set; apply H_no_lt_leftorright_eq_x_t; symmetry in Heq_t_x; tauto | idtac].
                  intros H_more_cumul_letteries_1_t_true.
                  assert (H_no_lt_leftorright_eq_t_x : lt_leftorright_eq t x -> Empty_set)
                    by (intros H_lt_leftorright_eq_t_x;
                        assert (J1 := (H_cumul_letteries_x_false _ H_lt_leftorright_eq_t_x) : cumul_letteries t = false);
                        rewrite J1 in H_more_cumul_letteries_1_t_true;
                        discriminate H_more_cumul_letteries_1_t_true).
                  assert (H_node_is_lettery_t := H_node_is_lettery _ H_more_cumul_letteries_1_t_true).
                  assert (H_no_lt_leftorright_eq_ft_fx : lt_leftorright_eq (f t) (f x) -> Empty_set)
                    by (intros; apply H_no_lt_leftorright_eq_t_x;
                        replace t with ((rev f) (f t)) by auto;
                        replace x with ((rev f) (f x)) by auto; apply H_node_is_lettery_t; assumption).
                  assert (H_lt_par_or_t_x : lt_par_or t x) by (apply lem002; assumption).

                  (**TWO CASES:
                     lt_leftorright_eq (f x) (f t) +  lt_leftorright_eq (f x) (f t) -> Empty_set
                        CASE LEFT: from lt_par_or x t and node_is_lettery f {y y' t} get lt_par_or {(f y) (f y')} (f t)
                                   then node_is_lettery f' (f t) from local-global transition
                                   then node_is_lettery (com_assoc f f') t by transitivity
                        CASE RIGHT: get remaining case lt_par_or (f x) (f t) 
                                    then apply IHx_par_node_is_lettery
                                    then node_is_lettery (com_assoc f f') t by transitivity **)
                destruct (lem003 (f x) (f t)) as [H_lt_leftorright_eq_fx_ft | H_no_lt_leftorright_eq_fx_ft].
                  * SearchAbout (lt_par _ _). (* lem009700_pre16:  forall (A : objects) (u x y : A),  lt_leftorright u y -> lt_par u x -> lt_par y x *)
                    Lemma lemm010 (A : objects) (u x y : nodes A)
                          (H_lt_leftorright_eq_u_y : lt_leftorright_eq u y)
                          (H_lt_par_x_u : lt_par x u)      
                    : lt_par x y.
                      induction H_lt_par_x_u;
                      destruct H_lt_leftorright_eq_u_y as [H_lt_leftorright_eq_u_y | [H_lt_leftorright_eq_u_y | H_lt_leftorright_eq_u_y]];
                      dependent destruction H_lt_leftorright_eq_u_y;
                      eauto (*auto for base step*).
                    Defined. Hint Resolve lemm010.

                    assert (H_lt_par_or_t_y: lt_par_or t y) by (destruct H_lt_par_or_t_x as [H_lt_par_or_t_x | H_lt_par_or_t_x]; [left; cut (lt_leftorright_eq x y); [intros Htemp; eapply (lemm010 Htemp H_lt_par_or_t_x); auto | auto ] | right; cut (lt_leftorright x y); [intros Htemp; eapply (lem009700_pre16 Htemp H_lt_par_or_t_x); auto | auto ]]).
                    assert (H_lt_par_or_t_y': lt_par_or t y') by (destruct H_lt_par_or_t_x as [H_lt_par_or_t_x | H_lt_par_or_t_x]; [left; cut (lt_leftorright_eq x y'); [intros Htemp; eapply (lemm010 Htemp H_lt_par_or_t_x); auto | auto] | right; cut (lt_leftorright x y'); [intros Htemp; eapply (lem009700_pre16 Htemp H_lt_par_or_t_x); auto | auto ]]).

                    Lemma lemm020 A B (f : arrows_assoc A B) (x y : nodes A) (H_node_is_lettery_x : node_is_lettery f x) (H_node_is_lettery_y : node_is_lettery f y) (H_lt_par_or_x_y : lt_par_or x y) : lt_par_or (f x) (f y).

                      assert (H_no_lt_leftorright_eq_x_y : lt_leftorright_eq x y -> Empty_set)
                        by (intros [ ?| [? |? ]]; apply (lem007200 H_lt_par_or_x_y); tauto).
                      assert (H_no_lt_leftorright_eq_y_x : lt_leftorright_eq y x -> Empty_set)
                        by (intros [ J1temp | [? |? ]]; apply (lem007200 H_lt_par_or_x_y); try symmetry in J1temp; tauto).
                      assert (H_no_lt_leftorright_eq_fx_fy : lt_leftorright_eq (f x) (f y) -> Empty_set)
                        by (intros; apply H_no_lt_leftorright_eq_x_y; replace x with ((rev f)(f x)) by auto; replace y with ((rev f)(f y)) by auto; apply H_node_is_lettery_x; assumption).
                      assert (H_no_lt_leftorright_eq_fy_fx : lt_leftorright_eq (f y) (f x) -> Empty_set)
                        by (intros; apply H_no_lt_leftorright_eq_y_x; replace x with ((rev f)(f x)) by auto; replace y with ((rev f)(f y)) by auto; apply H_node_is_lettery_y; assumption).
                      apply (lem002 H_no_lt_leftorright_eq_fx_fy H_no_lt_leftorright_eq_fy_fx).
                    Defined. Hint Resolve lemm020.


                    (* assert (H_node_is_lettery_t := H_node_is_lettery _ H_more_cumul_letteries_1_t_true : node_is_lettery f t).*)
                    assert (H_lt_par_or_ft_fy' : lt_par_or (f t) (f y')) by auto.
                    assert (H_lt_par_or_ft_fy : lt_par_or (f t) (f y)) by auto.

                    destruct H_lt_leftorright_eq_fx_ft as [H_lt_leftorright_eq_fx_ft | [H_lt_leftorright_eq_fx_ft | H_lt_leftorright_eq_fx_ft]].
                  - elimtype Empty_set; apply H_no_lt_leftorright_eq_x_t; left; replace x with ((rev f) (f x)) by auto; replace t with ((rev f) (f t)) by auto; rewrite H_lt_leftorright_eq_fx_ft; reflexivity.
                  - assert (H_lt_leftorright_eq_y_t : lt_leftorright_eq (f y) (f t)) by ( apply (lem010500 H_lt_left_once_fx_fy H_lt_leftorright_eq_fx_ft)). elimtype Empty_set; apply (lem007200  ((fun s => match s with | inl l => inr l | inr r => inl r end) H_lt_par_or_ft_fy)). decompose sum H_lt_leftorright_eq_y_t; auto.
                  - { Lemma lemm030 A (x y z : nodes A) (H_lt_right_x_y : lt_right x y) (H_lt_right_x_z : lt_right x z) (H_lt_par_y_z : lt_par y z) : lt_par (loc H_lt_right_x_y) (loc H_lt_right_x_z).

                        induction H_lt_right_x_y; dependent destruction H_lt_right_x_z; dependent destruction H_lt_par_y_z; simpl in *; auto. (** :D 1 ATTEMPT ONLY FYEAH **)
                      Defined. Hint Resolve lemm030.
                    (*TODO Lemma lemm040 A (x y z : nodes A) (H_lt_right_x_y : lt_right x y) (H_lt_right_x_z : lt_right x z) (H_lt_par_or_y_z : lt_par_or y z) : lt_par_or (loc H_lt_right_x_y) (loc H_lt_right_x_z).

                    induction H_lt_right_x_y; dependent destruction H_lt_right_x_z; destruct H_lt_par_or_y_z as [H_lt_par_or_y_z | H_lt_par_or_y_z]; dependent destruction H_lt_par_or_y_z; simpl in *; auto. (** :D 1 ATTEMPT ONLY FYEAH **)
                    Defined. Hint Resolve lemm040.*)

                      Lemma lemm050 A B C Dlist (x : nodes _) (H_lt_par_selfB_x : lt_par (at_right A (foldrightn (at_left (self B) C) Dlist)) x) : node_is_lettery (multi_bracket_left A B C Dlist) (x).
                      
                        split.
                        - induction Dlist as [ | D0 Dlist].
                          + { Lemma lemm060 A B C (x : nodes _) (H_lt_par_selfB_x : lt_par (at_right A (at_left (self B) C)) x) : node_is_lettery (bracket_left A B C) (x).
                          
                                split.
                                - dependent destruction x; [
                                    dependent destruction H_lt_par_selfB_x
                                  | dependent destruction H_lt_par_selfB_x
                                  | dependent destruction x; [
                                      repeat dependent destruction H_lt_par_selfB_x
                                    | repeat dependent destruction H_lt_par_selfB_x
                                    | intros z [J1 | [J1 | J1]]; (dependent destruction z; [
                                                                    repeat dependent destruction J1
                                                                  | repeat dependent destruction J1
                                                                  | dependent destruction z; [
                                                                      repeat dependent destruction J1
                                                                    | repeat dependent destruction J1
                                                                    | dependent destruction J1; simpl in *; auto; dependent destruction J1; simpl in *; auto ] ])
                                  ] ]. (** :D 1 ATTEMPT ONLY FYEAH **)
                                  
                                - intros z. replace ((rev (bracket_left A B C)) ((bracket_left A B C) z)) with z by auto. replace ((rev (bracket_left A B C)) ((bracket_left A B C) x)) with x by auto. revert z.
                                  dependent destruction x; [
                                      dependent destruction H_lt_par_selfB_x
                                    | dependent destruction H_lt_par_selfB_x
                                    | dependent destruction x; [
                                        repeat dependent destruction H_lt_par_selfB_x
                                      | repeat dependent destruction H_lt_par_selfB_x
                                      | intros z; dependent destruction z; [
                                          intros  [J1 | [J1 | J1]]; repeat dependent destruction J1
                                        | intros  [J1 | [J1 | J1]]; repeat dependent destruction J1
                                        | dependent destruction z; [
                                            intros  [J1 | [J1 | J1]]; repeat dependent destruction J1
                                          | intros  [J1 | [J1 | J1]]; repeat dependent destruction J1
                                          | intros  [J1 | [J1 | J1]]; dependent destruction J1; simpl in *; auto 9; dependent destruction J1; simpl in *; auto 9 ] ] ]].
                              Defined. Hint Resolve lemm060.

                              apply lemm060. assumption.
                            }
                          +  simpl in x. dependent destruction x.
                             * dependent destruction H_lt_par_selfB_x.
                             * dependent destruction H_lt_par_selfB_x.
                             * { dependent destruction H_lt_par_selfB_x; dependent destruction x. 
                                 - dependent destruction H_lt_par_selfB_x. 
                                 - dependent destruction H_lt_par_selfB_x.
                                   assert (H_lt_par_selfB_x_no_D0 : lt_par (at_right A (foldrightn (at_left (self B) C) Dlist)) (at_right A x)) by (constructor; assumption).
                                   intros z J2; simpl in z; dependent destruction z.
                                   * destruct J2 as [J2 | [J2 | J2]]; dependent destruction J2.
                                   * destruct J2 as [J2 | [J2 | J2]]; dependent destruction J2.
                                   * { dependent destruction z. 
                                       - destruct J2 as [J2 | [J2 | J2]]; do 2 dependent destruction J2.
                                       - assert ( J2_no_D0 : lt_leftorright_eq (at_right A x) (at_right A z) )
                                           by (destruct J2 as [J2 | [J2 | J2]]; dependent destruction J2;
                                               try (*for eq*) dependent destruction J2; auto 9).
                                         simpl.
                                         cut ( lt_leftorright_eq ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_right A x)) ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_right A z)) ); [
                                             intros [Htemp | [Htemp | Htemp]]; auto 9
                                           | idtac ].
                                         apply IHDlist; [exact H_lt_par_selfB_x_no_D0 | exact J2_no_D0].
                                       - destruct J2 as [J2 | [J2 | J2]]; do 2 dependent destruction J2.
                                     }
                                 - simpl.  intros z; dependent destruction z; [
                                             intros [J2 | [J2 | J2]]; dependent destruction J2
                                           | intros [J2 | [J2 | J2]]; dependent destruction J2
                                           | dependent destruction z; [ 
                                               intros [J2 | [J2 | J2]]; dependent destruction J2; dependent destruction J2
                                             | intros [J2 | [J2 | J2]]; dependent destruction J2; dependent destruction J2
                                             | intros [J2 | [J2 | J2]]; dependent destruction J2; try dependent destruction J2; simpl; auto 9 ] ].
                               }
                        - intros z. replace ((rev (multi_bracket_left A B C Dlist)) ((multi_bracket_left A B C Dlist) x)) with x by auto. replace ((rev (multi_bracket_left A B C Dlist)) ((multi_bracket_left A B C Dlist) z)) with z by auto. revert z.
                        induction Dlist as [ | D0 Dlist].
                          + intros z J1. replace x with ((rev (multi_bracket_left A B C nil)) ((multi_bracket_left A B C nil) x)) by auto. replace z with ((rev (multi_bracket_left A B C nil)) ((multi_bracket_left A B C nil) z)) by auto. revert z J1. apply lemm060. assumption.
                          + simpl in x. dependent destruction x.
                            * dependent destruction H_lt_par_selfB_x.
                            * dependent destruction H_lt_par_selfB_x.
                            * { dependent destruction H_lt_par_selfB_x; dependent destruction x. 
                                - dependent destruction H_lt_par_selfB_x. 
                                - dependent destruction H_lt_par_selfB_x.
                                  assert (H_lt_par_selfB_x_no_D0 : lt_par (at_right A (foldrightn (at_left (self B) C) Dlist)) (at_right A x)) by (constructor; assumption).
                                  intros z J2; simpl in z; dependent destruction z.
                                  *  cut ( lt_leftorright_eq (at_right A x)
                                                             (self (A /\ ((B /\ C) /\\ Dlist))) ); [
                                      intros [J3 | [J3 | J3]]; dependent destruction J3
                                    | idtac ];
                                     destruct J2 as [J2 | [J2 | J2]];
                                     simpl in J2; dependent destruction J2;
                                     apply IHDlist;
                                     auto. (** :D 2 ATTEMPTS ONLY **)
                                  (**/!\ the case [self] can be proved without IHDlist
                               + dependent destruction J2.
                               assert (J2_alt : (at_right A x0) = (self (A /\ (B /\ C) /\\ Dlist)) )
                               by (replace (at_right A x0) with (( rev (projT1 (multi_bracket_left_specif A B C Dlist)) ) ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_right A x0))) by auto;
                                 replace ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_right A x0));
                                 auto).
                               dependent destruction J2_alt. **)
                               (*Lemma lemmtemp A B C Dlist (x : nodes _) (J1 :  lt_left
         ((projT1 (multi_bracket_left_specif A B C Dlist)) (at_right A x))
         ((projT1 (multi_bracket_left_specif A B C Dlist))
            (self (A /\ (B /\ C) /\\ Dlist)))) : Empty_set.
                                 induction Dlist as [ | D0 Dlist].
                                 - simpl in *. dependent destruction x.
                                   + simpl in *. dependent destruction J1. Abort. *)
                                  * simpl in J2.
                                    cut ( lt_leftorright_eq (at_right A x)
                                                            (at_left z (((B /\ C) /\\ Dlist) )) ); [
                                        intros [J3 | [J3 | J3]]; dependent destruction J3
                                      | idtac ];
                                    destruct J2 as [J2 | [J2 | J2]];
                                    simpl in J2; dependent destruction J2;
                                    apply IHDlist;
                                    auto. (** :D 1 ATTEMPT ONLY **) Show.
                                  * { dependent destruction z. 
                                      - destruct J2 as [J2 | [J2 | J2]]; simpl in J2; do 2 dependent destruction J2.
                                      - simpl in J2. (**/1\ AGAIN TWISTING TECHNIQUE **)
                                        cut ( lt_leftorright_eq (at_right A x)
                                                                (at_right A (z)) ); [
                                            intros [J3 | [J3 | J3]]; dependent destruction J3; auto 9
                                          | idtac ].
                                        destruct J2 as [J2 | [J2 | J2]];
                                          simpl in J2; dependent destruction J2;
                                          apply IHDlist;
                                          auto.
                                      - destruct J2 as [J2 | [J2 | J2]]; simpl in J2; do 2 dependent destruction J2.
                                    }
                                - simpl. intros z; dependent destruction z; [
                                           intros [J2 | [J2 | J2]]; dependent destruction J2
                                         | intros [J2 | [J2 | J2]]; dependent destruction J2
                                         | dependent destruction z; [ 
                                             intros [J2 | [J2 | J2]]; dependent destruction J2; dependent destruction J2
                                           | intros [J2 | [J2 | J2]]; dependent destruction J2; dependent destruction J2
                                           | intros [J2 | [J2 | J2]]; simpl in J2; dependent destruction J2; auto 9 ] ]. (** :D 1 ATTEMPT ONLY **)
                              }
                      Defined. Hint Resolve lemm050.
                         
                      Lemma lemm070 A B C Dlist (t : nodes _) (H_lt_right_self_t : lt_right (self _) t) (H_lt_par_t_selfB : lt_par t (at_right A (foldrightn (at_left (self B) C) Dlist))) : Empty_set.
                           
                        dependent destruction H_lt_right_self_t; dependent destruction H_lt_par_t_selfB.
                        induction Dlist as [ | D0 Dlist].
                        -  simpl in z; dependent destruction z; [
                             dependent destruction H_lt_par_t_selfB
                           | dependent destruction H_lt_par_t_selfB;
                             destruct z; dependent destruction H_lt_par_t_selfB
                           | dependent destruction H_lt_par_t_selfB ]. 
                        - simpl in z; dependent destruction z; [
                            dependent destruction H_lt_par_t_selfB
                          | dependent destruction H_lt_par_t_selfB;
                            eapply IHDlist; eassumption
                          | dependent destruction H_lt_par_t_selfB ].
                      Defined. Hint Resolve lemm070.
                         
                      assert (H_lt_leftorright_eq_fx_ft_loc : lt_right (self _) (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft))).
                      cut (lt_right (self _) ((loc H_lt_leftorright_eq_fx_ft))); [
                          idtac
                        | auto ].
                      rewrite <- H_list_E2_nodes_self.
                      intros Htemp; replace (loc H_lt_leftorright_eq_fx_ft) with (nodes_map H_same_object_at_node (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft))  ) in Htemp by (apply lem062; reflexivity); revert Htemp.
                      SearchPattern (lt_right (nodes_map _ _) (nodes_map _ _) -> lt_right _ _).
                      SearchPattern (lt_right (nodes_map _ _) (nodes_map _ _)).
                      SearchPattern (lt_right (lem071 _ _) (lem071 _ _) -> lt_right _ _).
                      SearchPattern (lt_right (lem071 _ _) (lem071 _ _)).
                         (**/!\ lemm080 is necessary for [right] [right] transfer **)
                      Lemma lemm080 A A' (H_objects_same : objects_same A A') (x y : nodes A) (H_lt_right : lt_right (nodes_map H_objects_same x) (nodes_map H_objects_same y)) : lt_right x y.
                        induction H_objects_same.
                        - simpl in *; assumption.
                        - dependent destruction x; dependent destruction y; 
                          solve [ constructor
                                | dependent destruction H_lt_right
                                | constructor; dependent destruction H_lt_right;
                                  apply IHH_objects_same1; assumption
                                | constructor; dependent destruction H_lt_right;
                                  apply IHH_objects_same2; assumption ].
                      Defined. Hint Resolve lemm080.

                      apply lemm080.

                      Lemma lemm090 A A' (H_objects_same : objects_same A A') (x y : nodes A)(H_lt_par_x_y : lt_par x y) : lt_par (nodes_map H_objects_same x) (nodes_map H_objects_same y).
                        induction H_objects_same.
                        - simpl; assumption.
                        - dependent destruction x; dependent destruction y;
                          solve [ constructor
                                | dependent destruction H_lt_par_x_y
                                | constructor; dependent destruction H_lt_par_x_y;
                                  apply IHH_objects_same1; assumption
                                | constructor; dependent destruction H_lt_par_x_y;
                                  apply IHH_objects_same2; assumption ]. (** :D 1 ATTEMPT ONLY FYEAH **)
                      Defined. Hint Resolve lemm090.

                      { destruct H_lt_par_or_ft_fy' as [H_lt_par_ft_fy' | H_lt_par_ft_fy'].
                        - elimtype Empty_set.
                          assert ( H_lt_par_ft_fy'_loc : lt_par (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft)) (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr)))) ).
                          { replace (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr))))
                            with (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_right_fx_fy')) 
                              by (apply lem061; exact H_list_E2_nodes).
                            apply lemm090. apply lemm030. auto. 
                          }
                          apply (lemm070 _ _ _ H_lt_leftorright_eq_fx_ft_loc H_lt_par_ft_fy'_loc).
                        - assert ( H_lt_par_fy'_ft_loc : lt_par (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr)))) (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft)) ).
                          { replace (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr))))
                            with (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_right_fx_fy')) 
                              by (apply lem061; exact H_list_E2_nodes).
                            apply lemm090. apply lemm030. auto. 
                          }
                          
                          Check ((*H_node_is_lettery_ft :=*) lemm050 _ _ _ H_lt_par_fy'_ft_loc).
                          apply lem068.
                          + exact H_node_is_lettery_t. 
                          + assert (Jtemp: cats H_term_arrow_f' (loc H_lt_leftorright_eq_fx_ft) = (f t)).
                            { rewrite lem059.
                              SearchRewrite (loc_rev _ (loc _)). (*return lem543*)
                              Check (loc H_lt_leftorright_eq_fx_ft). 
                              Check (cats H_term_arrow_f' (self (object_at_node (f x)))).
                              (**OLD for debug assert ((cats H_term_arrow_f' (self (object_at_node (f x)))) = (f x)) by .. .**)
                              Lemma lemm100 A (x y : nodes A) (Heq : x = y) : (objects_same (object_at_node y) (object_at_node x)).
                                rewrite Heq. exact (objects_same_refl _).
                              Defined. Hint Unfold lemm100.
                              Lemma lemm110 A (x y : nodes A) (Heq : x = y) (z : nodes (object_at_node y)) : loc_rev x (nodes_map (lemm100 Heq) z) = loc_rev y z.
                                rewrite Heq. unfold lemm100. simpl.  
                                SearchRewrite (nodes_map (objects_same_refl _) _). 
                                rewrite lem212. reflexivity. 
                              Defined. Hint Resolve lemm110. Hint Rewrite lemm110 using eauto.
                              Lemma lemm120 A (H_objects_same : objects_same A A) : H_objects_same = objects_same_refl A.
                                dependent induction H_objects_same.
                                - simpl. reflexivity.
                                - simpl. rewrite IHH_objects_same1. rewrite IHH_objects_same2. reflexivity.
                              Defined.
                              Lemma lemm130 A B (H_objects_same_1 : objects_same A B) (H_objects_same_2 : objects_same A B) : H_objects_same_1 = H_objects_same_2.
                                dependent induction H_objects_same_1.
                                - simpl. dependent destruction H_objects_same_2. reflexivity.
                                - simpl. dependent destruction H_objects_same_2.
                                  rewrite (IHH_objects_same_1_1 H_objects_same_2_1).
                                  rewrite (IHH_objects_same_1_2 H_objects_same_2_2). reflexivity.
                              Defined. Hint Resolve lemm130.
                              replace (objects_same_term_arrow_source H_term_arrow_f') with (lemm100 IHx_cats_self) by (*auto*) apply lemm130.
                              rewrite (lemm110 IHx_cats_self).
                              (*repeat SearchRewrite (loc_rev _ (loc _)). (*return lem543*)*)
                              rewrite lem543. reflexivity.
                            }
                            rewrite <- Jtemp. apply lem058.
                            Lemma lemm140 A B (f : arrows A B) A' (H_objects_same : objects_same A A') : forall  (x : nodes A') (J : node_is_lettery f (nodes_map (objects_same_sym H_objects_same) x)), node_is_lettery (lem070 f H_objects_same) x.
                              split.
                              - destruct J as (J & _).
                                unfold lem070. simpl. rewrite <- lem072 in J.
                                intros z J2. apply J. auto.
                              - destruct J as (_ & J).
                                unfold lem070. simpl. rewrite <- lem072 in J.
                                intros z J2.
                                Lemma lemm150 A A' (H_objects_same : objects_same A A') : rev (lem071 H_objects_same) = lem071 (objects_same_sym H_objects_same).
                                  induction H_objects_same.
                                  - simpl. reflexivity.
                                  - simpl. f_equal; [assumption | assumption].
                                Defined. Hint Resolve lemm150. Hint Rewrite lemm150 using eauto.
                                rewrite lemm150.
                                cut (lt_leftorright_eq ( ((rev f) (f ((lem071 H_objects_same) x))))
                                                       ( ((rev f) (f ((lem071 H_objects_same) z))))); [
                                    auto
                                  | apply J; exact J2 ].
                            Defined. Hint Resolve lemm140.
                            
                            apply lemm140. exact ((*H_node_is_lettery_ft := *)lemm050 _ _ _ H_lt_par_fy'_ft_loc).
                      }
                    }
                    * assert (H_lt_par_or_ft_fx : lt_par_or (f t) (f x)) by auto.
                      apply lem068.
                  - exact H_node_is_lettery_t.
                  - apply IHx_par_node_is_lettery. exact H_lt_par_or_ft_fx.
            }
            }

            Hint Rewrite lem072 lem073 using eauto.
            
            (**STEP**)
            assert (H_object_at_node_more: forall x : B,
                      H_more_cumul_letteries_1 x = true ->  object_at_node x = object_at_node ((com_assoc f f') x)).
            {
              intros t. unfold H_more_cumul_letteries_1. unfold projT1. unfold H_more_cumul_letteries.
              unfold more_cumul_letteries.
              destruct (lem003 x t) as [H_lt_leftorright_eq_x_t | H_no_lt_leftorright_eq_x_t].
              + intros _. apply H_object_at_node_x_all_full. assumption.
              + destruct (nodes_eq_dec t x) as [Heq_t_x | Heq_no_t_x]; [elimtype Empty_set; apply H_no_lt_leftorright_eq_x_t; symmetry in Heq_t_x; tauto | idtac].
                intros H_more_cumul_letteries_1_t_true.
                assert (H_no_lt_leftorright_eq_t_x : lt_leftorright_eq t x -> Empty_set)
                  by (intros H_lt_leftorright_eq_t_x;
                  assert (J1 := (H_cumul_letteries_x_false _ H_lt_leftorright_eq_t_x) : cumul_letteries t = false);
                  rewrite J1 in H_more_cumul_letteries_1_t_true;
                  discriminate H_more_cumul_letteries_1_t_true).
                assert (H_object_at_node_t := H_object_at_node _ H_more_cumul_letteries_1_t_true).
                assert (H_node_is_lettery_t := H_node_is_lettery _ H_more_cumul_letteries_1_t_true).
                assert (H_no_lt_leftorright_eq_ft_fx : lt_leftorright_eq (f t) (f x) -> Empty_set)
                    by (intros; apply H_no_lt_leftorright_eq_t_x;
                        replace t with ((rev f) (f t)) by auto;
                        replace x with ((rev f) (f x)) by auto; apply H_node_is_lettery_t; assumption).
                assert (H_lt_par_or_t_x : lt_par_or t x) by (apply lem002; assumption).
                (**TWO CASES:
                     lt_leftorright_eq (f x) (f t) +  lt_leftorright_eq (f x) (f t) -> Empty_set
                        CASE LEFT: from lt_par_or x t and node_is_lettery f {y y' t} get lt_par_or {(f y) (f y')} (f t)
                                   then object_at_node (f t) = object_at_node (f' (f t)) from local-global transition
                                   then object_at_node (t) = object_at_node (f t) = object_at_node (f' (f t)) by transitivity
                        CASE RIGHT: get remaining case lt_par_or (f x) (f t) 
                                    then apply IHx_par_object_at_node to get object_at_node (f t) = object_at_node (f' (f t))
                                    then object_at_node (t) = object_at_node (f t) = object_at_node (f' (f t)) by transitivity **)
                destruct (lem003 (f x) (f t)) as [H_lt_leftorright_eq_fx_ft | H_no_lt_leftorright_eq_fx_ft].
                *
                { (** getting lt_par_or x t and node_is_lettery f {y y' t} get lt_par_or {(f y) (f y')} (f t) **)
                  assert (H_lt_par_or_t_y: lt_par_or t y) by (destruct H_lt_par_or_t_x as [H_lt_par_or_t_x | H_lt_par_or_t_x]; [left; cut (lt_leftorright_eq x y); [intros Htemp; eapply (lemm010 Htemp H_lt_par_or_t_x); auto | auto] | right; cut (lt_leftorright x y); [intros Htemp; eapply (lem009700_pre16 Htemp H_lt_par_or_t_x); auto | auto]]).
                  assert (H_lt_par_or_t_y': lt_par_or t y') by (destruct H_lt_par_or_t_x as [H_lt_par_or_t_x | H_lt_par_or_t_x]; [left; cut (lt_leftorright_eq x y' ); [intros Htemp; eapply (lemm010 Htemp H_lt_par_or_t_x); auto | auto] | right; cut (lt_leftorright x y'); [intros Htemp; eapply (lem009700_pre16 Htemp H_lt_par_or_t_x); auto | auto]]).
                  assert (H_lt_par_or_ft_fy' : lt_par_or (f t) (f y')) by auto.
                  assert (H_lt_par_or_ft_fy : lt_par_or (f t) (f y)) by auto.
                  
                  (** getting object_at_node (f t) = object_at_node (f' (f t)) from local-global transition **)
                  destruct H_lt_leftorright_eq_fx_ft as [H_lt_leftorright_eq_fx_ft | [H_lt_leftorright_eq_fx_ft | H_lt_leftorright_eq_fx_ft]].
                  - elimtype Empty_set; apply H_no_lt_leftorright_eq_x_t; left; replace x with ((rev f) (f x)) by auto; replace t with ((rev f) (f t)) by auto; rewrite H_lt_leftorright_eq_fx_ft; reflexivity.
                  - assert (H_lt_leftorright_eq_y_t : lt_leftorright_eq (f y) (f t)) by ( apply (lem010500 H_lt_left_once_fx_fy H_lt_leftorright_eq_fx_ft)). elimtype Empty_set; apply (lem007200  ((fun s => match s with | inl l => inr l | inr r => inl r end) H_lt_par_or_ft_fy)). decompose sum H_lt_leftorright_eq_y_t; auto.
                  - (**TODO erase lemm040 above **)
                    (**comparable to lem064 above**)
                    Lemma lemm160 A B C Dlist (x : nodes _) (H_lt_par_selfB_x : lt_par (at_right A (foldrightn (at_left (self B) C) Dlist)) x) : object_at_node x = object_at_node ((multi_bracket_left A B C Dlist) (x)).
                    
                    Lemma lemm170 A B C (x : nodes _) (H_lt_par_selfB_x : lt_par (at_right A (at_left (self B) C)) x) : object_at_node x = object_at_node ((bracket_left A B C) (x)).
                      
                      dependent destruction x; [
                        dependent destruction H_lt_par_selfB_x
                      | dependent destruction H_lt_par_selfB_x
                      | dependent destruction x; [
                          repeat dependent destruction H_lt_par_selfB_x
                        | repeat dependent destruction H_lt_par_selfB_x
                        | simpl; reflexivity
                      ] ]. (** :D 1 ATTEMPT ONLY FYEAH **)
                    Defined. Hint Resolve lemm170. Hint Rewrite <- lemm170 using eauto.

                    induction Dlist as [ | D0 Dlist].
                    + apply lemm170. assumption.
                    + simpl in x. dependent destruction x.
                      * dependent destruction H_lt_par_selfB_x.
                      * dependent destruction H_lt_par_selfB_x.
                      * { dependent destruction H_lt_par_selfB_x; dependent destruction x. 
                          - dependent destruction H_lt_par_selfB_x. 
                          - dependent destruction H_lt_par_selfB_x.
                            assert (H_lt_par_selfB_x_no_D0 : lt_par (at_right A (foldrightn (at_left (self B) C) Dlist)) (at_right A x)) by (constructor; assumption).
                            simpl. rewrite <- IHDlist. 
                            + simpl. reflexivity.
                            + exact H_lt_par_selfB_x_no_D0.
                          - simpl. reflexivity.
                        }
                    Defined. Hint Resolve lemm160. Hint Rewrite <- lemm160 using eauto.

                    assert (H_lt_leftorright_eq_fx_ft_loc : lt_right (self _) (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft))).
                    { cut (lt_right (self _) ((loc H_lt_leftorright_eq_fx_ft))); [
                        idtac
                      | auto ].
                      rewrite <- H_list_E2_nodes_self.
                      intros Htemp; replace (loc H_lt_leftorright_eq_fx_ft) with (nodes_map H_same_object_at_node (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft))  ) in Htemp by (apply lem062; reflexivity); revert Htemp.
                      apply lemm080.
                    }

                    { destruct H_lt_par_or_ft_fy' as [H_lt_par_ft_fy' | H_lt_par_ft_fy'].
                      - elimtype Empty_set.
                        assert ( H_lt_par_ft_fy'_loc : lt_par (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft)) (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr)))) ).
                        { replace (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr))))
                          with (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_right_fx_fy')) 
                            by (apply lem061; exact H_list_E2_nodes).
                          apply lemm090. apply lemm030. auto. 
                        }
                        apply (lemm070 _ _ _ H_lt_leftorright_eq_fx_ft_loc H_lt_par_ft_fy'_loc).

                      - assert ( H_lt_par_fy'_ft_loc : lt_par (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr)))) (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft)) ).
                        { replace (at_right E1 (foldrightn (at_left (self (object_at_node (loc H_lt_right_fx_fy'))) (projT1 mfr)) (projT1 (projT2 mfr))))
                          with (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_right_fx_fy')) 
                            by (apply lem061; exact H_list_E2_nodes).
                          apply lemm090. apply lemm030. auto. 
                        }

                        Check ((*H_object_at_node_ft :=*) lemm160 _ _ _ H_lt_par_fy'_ft_loc).
                        simpl.  transitivity (object_at_node (f t)).
                        + exact H_object_at_node_t.
                        + (* comparable to assert (H_object_at_node_fy' : object_at_node (f y') = object_at_node (f' (f y'))). above *)
                          rewrite (H_eq_f'y' _ H_lt_leftorright_eq_fx_ft).
                          (* objects_same_term_arrow_post1 : objects_same (object_at_node x) (object_at_node (H_term_arrow_f'_f x)). *)
                          rewrite <- (fun H x => objects_eq_same (objects_same_term_arrow_post1 H x)).
                          unfold lem070. simpl arrows_assoc_on_nodes.
                          (* lem072:  (lem071 H_objects_same) x = nodes_map (objects_same_sym H_objects_same) x *)
                          rewrite lem072.
                          rewrite <- (lem121 H_lt_leftorright_eq_fx_ft).
                          SearchRewrite (object_at_node (_)).
                          (* lem011:  object_at_node ((lem071 H_objects_same) x) = object_at_node x *)
                          (** this is comparable to lem011 above, more immediate for nodes_map .. **)
                          Lemma lemm180 (A A' : objects) (H_objects_same : objects_same A A') (x : A)
                          : object_at_node (nodes_map H_objects_same x) = object_at_node x.
                            SearchRewrite (objects_same_sym _).
                            Lemma lemm190 (A A' : objects) (H_objects_same : objects_same A A')
                                  : objects_same_sym (objects_same_sym H_objects_same) = H_objects_same.
                              induction H_objects_same; simpl in *; auto. (* :D 1 ATTEMPT ONLY *)
                            Defined. Hint Resolve lemm190. Hint Rewrite lemm190 using eauto.
                            replace H_objects_same with (objects_same_sym (objects_same_sym H_objects_same)) by auto.
                            rewrite <- lem072. rewrite lem011. reflexivity.
                          Defined. Hint Resolve lemm180. Hint Rewrite lemm180 using eauto.
                          (*ALT: rewrite <- (lemm180 (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft)).*)
                          replace (object_at_node (loc H_lt_leftorright_eq_fx_ft)) with (object_at_node (nodes_map (objects_same_sym H_same_object_at_node) (loc H_lt_leftorright_eq_fx_ft))) by (*auto*) apply lemm180.
                          exact ((*H_object_at_node_ft :=*) lemm160 _ _ _ H_lt_par_fy'_ft_loc).
                     }     
                }
                * assert (H_lt_par_or_ft_fx : lt_par_or (f t) (f x)) by auto.
                  simpl. transitivity (object_at_node (f t)).
                  - exact H_object_at_node_t.
                  - apply IHx_par_object_at_node. exact H_lt_par_or_ft_fx.
            }

           (**STEP**)
            assert (H_cumul_B_more :  forall t z : B, lt_right t z -> lt_right ((com_assoc f f') t) ((com_assoc f f') z)).
            { intros t z H_lt_right_t_z; destruct (nodes_eq_dec t x) as [Heq_t_x | Heq_no_t_x].
              + subst t. simpl. 
                Check H_node_is_lettery_x_all_full. Check H_node_is_lettery_y'_full.
                assert (H_lt_leftorright_eq_y'_t : lt_leftorright_eq y' z) by ( apply (lem010600 H_lt_right_once_x_y' H_lt_right_t_z)).
                cut (lt_right (f' (f x)) (f' (f y'))); [
                    intros H_lt_right_f'fx_f'fy'; apply (lem00710' H_lt_right_f'fx_f'fy'); clear H_lt_right_f'fx_f'fy'
                  | auto ].
                apply H_node_is_lettery_y'_full. exact H_lt_leftorright_eq_y'_t.
              + assert (Heq_no_ft_fx : f t = f x -> Empty_set) by (intros J1; exfalso; apply Heq_no_t_x; replace t with ((rev f) (f t)) by auto; replace x with ((rev f) (f x)) by auto; rewrite J1; reflexivity).
                simpl.  assert (H_lt_right_ft_fz : lt_right (f t) (f z)) by (apply H_cumul_B; exact H_lt_right_t_z).
                apply H_cumul_lt_right_A; assumption.
            }


            exact ( (IHlen H_more_cumul_letteries_1 H_more_cumul_letteries_2 H_more_cumul_letteries_5_satur H_more_cumul_letteries_4 M (com_assoc f f') H_node_is_lettery_more H_object_at_node_more H_cumul_B_more) <o f').
            Guarded.
}
Defined.


Definition lem008200' A (x : nodes A) : node_is_letter x + node_is_tensor x.

exact (lem008100 (object_at_node x)).
Defined. Hint Resolve lem008200'.

Definition lemm200 A (x : nodes A) : node_is_letter x + (node_is_letter x -> Empty_set).

assert (H_dec : node_is_letter x + node_is_tensor x) by apply lem008200'.
destruct H_dec as [H_dec | H_dec].
- left; exact H_dec.
- right; intros J1; apply (lem008300 _ J1 H_dec).
Defined. Hint Resolve lemm200.

Definition cumul_letters A (x : nodes A) : bool.

assert (H_dec : node_is_letter x + (node_is_letter x -> Empty_set)) by apply lemm200.
destruct H_dec as [H_dec | H_dec].
- exact true.
- exact false.
Defined. Hint Unfold cumul_letters.

Definition H_cumul_letters_wellform A : cumul_letteries_wellform' A (@cumul_letters A).

intros x H_node_is_letter_x. induction x; [destruct A | idtac | idtac].
- reflexivity.
- dependent destruction H_node_is_letter_x.
- (* auto = *) apply IHx. exact H_node_is_letter_x.
- apply IHx. exact H_node_is_letter_x.
Defined.

Lemma H_cumul_letters_wellform_rev A (x : nodes A) (H_cumul_letters_x_true : cumul_letters x = true) : node_is_letter x.

induction x; [destruct A | idtac | idtac].
- constructor.
- dependent destruction H_cumul_letters_x_true.
- simpl in *. apply IHx. exact H_cumul_letters_x_true.
- simpl in *. apply IHx. exact H_cumul_letters_x_true.
Defined.

Definition H_cumul_letters_satur A (y : nodes A) (H_cumul_letters_y : cumul_letters y = true )
           (z : nodes A) (H_lt_leftorright_eq_y_z : lt_leftorright_eq y z)
: cumul_letters z = true.

apply H_cumul_letters_wellform.
apply H_cumul_letters_wellform_rev in H_cumul_letters_y.
eapply lem008600; eassumption.
(*induction y.
- dependent destruction H_cumul_letters_y. simpl in *. subst A.
  destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]];
    dependent destruction H_lt_leftorright_eq_y_z; auto.
- dependent destruction z;
  destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]];
  dependent destruction H_lt_leftorright_eq_y_z;
  (apply IHy; [assumption | tauto]).
- dependent destruction z;
  destruct H_lt_leftorright_eq_y_z as [H_lt_leftorright_eq_y_z | [H_lt_leftorright_eq_y_z | H_lt_leftorright_eq_y_z]];
  dependent destruction H_lt_leftorright_eq_y_z;
  (apply IHy; [assumption | tauto]).*)
Defined.

Definition len_cumul_letters A := (lengthn'' (@cumul_letters A) (@H_cumul_letters_wellform A)).

Definition H_cumul_letters_len A : (lengthn'' (@cumul_letters A) (@H_cumul_letters_wellform A)) <= @len_cumul_letters A.

constructor. Show Proof.
Defined.

Lemma H_cumul_letters_object_at_node B A (f : arrows_assoc B A)  (x : nodes B) (H_cumul_letters_x_true : cumul_letters x = true)
: object_at_node x = object_at_node (f x).

apply H_cumul_letters_wellform_rev in H_cumul_letters_x_true.
dependent destruction H_cumul_letters_x_true.
erewrite lem005300; symmetry; eassumption.
Defined.

Lemma H_cumul_letters_node_is_lettery B A (f : arrows_assoc B A) (x : nodes B) (H_cumul_letters_x_true : cumul_letters x = true)
: node_is_lettery f x.

apply H_cumul_letters_wellform_rev in H_cumul_letters_x_true.
apply lem008700. exact H_cumul_letters_x_true.
Defined.

Lemma lemma_completeness : forall (B A : objects) (f : arrows_assoc B A)
                                  (H_cumul_lt_right_B : forall x y : nodes B, lt_right x y -> lt_right (f x) (f y))
                           , arrows A B.

intros. apply ( @lem005700 B (@len_cumul_letters B) (@cumul_letters B) (@H_cumul_letters_wellform B) (@H_cumul_letters_satur B) (@H_cumul_letters_len B) A f (@H_cumul_letters_node_is_lettery B A f) (@H_cumul_letters_object_at_node B A f) H_cumul_lt_right_B ).
Defined.

(**ADDENDUM**)
Lemma lem004510 : forall A B (f: arrows A B), bracket_left_occurs_in f + bracket_left_not_occurs_in f.

induction f; simpl in *; intuition.
Defined. Hint Resolve lem004510.
