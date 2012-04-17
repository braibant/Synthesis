Require Import String. 

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X ident, A at level 100, B at level 200). 
Axiom admit : forall {X} , X. 

Definition ident := string. 

Section var.   
  Variable T : Type. 
  Inductive var : list T -> T -> Type :=
  | var_0 : forall E t , var (cons t E) t
  | var_S : forall E t t' , var E t' -> var (cons t E) t'. 

  Variable eval_type : T -> Type. 

  Fixpoint eval_env E : Type :=
    match E with 
        nil => unit
      | cons t q => (eval_type t * eval_env q)%type
    end. 

  Fixpoint get E t (v: var E t): eval_env E -> eval_type t :=
    match v with 
      | var_0  _ _ => fun e => (fst e)
      | var_S _ _ _ v => fun e => get _ _ v (snd e)
    end. 

  Fixpoint append_envs E F : eval_env E -> eval_env F -> eval_env (List.app E F) :=
    match E with 
      | nil => fun _ (x : eval_env F) => x 
      | cons t q => fun (X : eval_type t * eval_env q) Y => 
                     let (A,B) := X in (A, append_envs q F B Y)
    end. 
End var. 

Arguments var {T} _ _. 
Arguments var_0 {T} {E} {t}. 
Arguments var_S {T} {E} {t} {t'} _. 
Arguments get {T eval_type} E t _ _. 
Arguments append_envs {T eval_type} E F _ _. 
Arguments eval_env {T} _ _ .  

Section dependent_lists. 
  Variable T : Type. 
  Variable P : T -> Type. 
  Inductive dlist  : list T -> Type := 
      | dlist_nil : dlist  nil
      | dlist_cons : forall (t : T) q, P t -> dlist q -> dlist (cons t q).  
  
  Variable E : T -> Type.

  Definition EVAL l := eval_env E l. 
  Variable F : forall (t : T), P t -> E t -> option (E t). 
  Fixpoint dlist_fold (l : list T) (d : dlist l) : EVAL l -> option (EVAL l):=
    match d with
        dlist_nil => fun v => Some v
      | dlist_cons t q pt dlq => 
          fun v => 
            do x <- F t pt (fst v);
            do y <- dlist_fold q dlq (snd v);
            Some (x,y)
    end. 
End dependent_lists. 

Module Abstract. 
  Record T :=
    {
      carrier :> Type;
      eqb : carrier -> carrier -> bool;
      lt  : carrier -> carrier -> bool
    }. 
End Abstract. 

Require Import ZArith. 

(** Implementation of parametric size machine words.  *)
Module Word. 
  
  Record T n := mk { val :> Z ; 
                     range : (0 <= val < two_power_nat n)%Z}. 
  Arguments val {n} _. 
  Arguments range {n} _. 
  
  Notation "[2^ n ]" := (two_power_nat n). 
  
  Open Scope Z_scope. 
  
  Lemma mod_in_range n:
    forall x, 0 <= Zmod x [2^ n] < [2^ n] .
  Proof.
    intro.
    apply (Z_mod_lt x).
    reflexivity. 
  Qed.
  
  Definition repr n (x: Z)  : T n := 
    mk n (Zmod x [2^ n]) (mod_in_range n x ).
  

  Definition add {n} : T n -> T n -> T n := fun x y => repr n (x + y ). 
  Definition minus {n} : T n -> T n -> T n := fun x y => repr n (x - y). 
  Definition mult {n} : T n -> T n -> T n := fun x y => repr n (x * y).  
  Definition eq {n} : T n -> T n -> bool := 
    fun x y => 
      (match val x ?= val y with Eq => true | _ => false end) .

  Definition lt {n} : T n -> T n -> bool :=
    fun x y => 
      (match val x ?= val y with Lt => true | _ => false end) .

End Word. 
 
Module FIFO. 
  Section t. 
    Variable X : Type. 
    Definition T := list X. 
    
    Definition push x (q : T) : T := 
      List.app q (cons x nil). 
        
    Definition first (q : T) : option X := 
      match q with 
        | nil => None
        | cons t q => Some t
      end. 
    
    Definition pop (q : T) := 
      match q with 
          | nil => None
          | cons t q => Some q
      end.

    Definition isempty (q : T) :=
      match q with 
          | nil => true
          | _ => false
      end. 

    Definition isfull (q : T) := false. 
    
    Definition clear (q : T) : T := nil. 
  End t. 
End FIFO. 

Module Regfile. 
  Section t. 
    Axiom T : Z -> Type -> Type. 
    Axiom empty : forall size D, T size D.
    Axiom get : forall size D, T size D -> Z -> option D.
    Axiom set : forall size D, T size D -> Z -> D -> option (T size D).
    
    
  End t. 
End Regfile. 

(* The base types, that exist in every language. These types should have:
   - decidable equality; 
   - default element (to initialize the arrays)
 *)
Inductive type0 : Type :=
| Tunit : type0 
| Tbool: type0 
| Tint: nat -> type0
| Tabstract : ident -> Abstract.T -> type0. 

Fixpoint eval_type0 st : Type := 
  match st with 
    | Tunit => unit
    | Tbool => bool
    | Tint n => Word.T n
    | Tabstract _ t => Abstract.carrier t
  end. 

Definition eval_type0_list l : Type := eval_env eval_type0 l. 

(** Operations on types *)
Section type_ops. 
  
  Definition eqb_bool (b1 b2: bool)  :=
    match b1,b2 with 
      | true, true => true
      | false, false => true
      | _,_ => false
    end. 
  
  Fixpoint type0_eq(t : type0) : eval_type0 t -> eval_type0 t -> bool :=
    match t with 
      | Tunit => fun _ _  => true
      | Tint n => @Word.eq n
      | Tbool  => eqb_bool 
      | Tabstract _ t => Abstract.eqb t
    end. 
  
  
  Definition ltb_bool a b :=
    match a, b with
      | false, true => true
      | _, _ => false
    end. 
  
  Fixpoint type0_lt (bt : type0) : eval_type0 bt -> eval_type0 bt -> bool :=
    match bt with
      | Tunit => fun _ _  => true
                              
      | Tbool => ltb_bool 
      | Tint n => @Word.lt n
      | Tabstract _ t => Abstract.lt t
    end. 
End type_ops. 

Require Import ZArith.
 
Record signature :=
  {
    args : list type0;
    res : type0; 
    value : eval_type0_list args -> eval_type0 res
  }. 

(* could it be a primitive with an empty set of arguments ? *)
Record constant :=
  {
    cst_ty :> type0;
    cst_val : eval_type0 cst_ty
  }. 

Definition Cbool b : constant := Build_constant Tbool b. 
Definition Cword {n} x : constant := Build_constant (Tint n) (Word.repr _ x). 


Module BS. 

  Inductive type1 : Type :=
    | T01 : type0 -> type1
    | Tunion : forall (idx : ident), type1_id_list -> type1
    | Ttuple : list type1 -> type1
                             with type1_id_list :=
    | type1_id_list_nil : type1_id_list 
    | type1_id_list_cons : ident -> type1 -> type1_id_list ->  type1_id_list. 
                       
  Inductive type2 :=
    | Treg : type1 -> type2
    | Tregfile  : Z -> type1 -> type2
    | Tfifo : type1 -> type2. 

  (** [eval_type t] computes the coq denotation of the [type] [t] *)
  Fixpoint eval_type1  (t : type1 ) : Type :=
    match t with
      | T01 st => eval_type0 st 
      | Tunion  _ cases => eval_type1_id_list (sum)%type  cases
      | Ttuple  x => 
          eval_env eval_type1 x
    end
      with 
      eval_type1_id_list (op : Type -> Type -> Type)  (l : type1_id_list ) : Type :=
    match l with 
      | type1_id_list_nil => unit
      | type1_id_list_cons  name t q => op (eval_type1  t) (eval_type1_id_list op  q)%type
    end. 
  
  Definition eval_type2 (t : type2) : Type :=
    match t with 
        Treg t => eval_type1 t
      | Tregfile n b => Regfile.T n (eval_type1 b)
      | Tfifo st => FIFO.T (eval_type1 st)
    end. 

  Definition eval_type2_list  l := eval_env  eval_type2 l. 
    
  Notation "x :: q" := (cons  x q). 
  Definition T02 x := Treg (T01 x). 
  
  Definition lift := List.map T02. 
  Notation B := Tbool. 
  Notation W n := (Tint n).

  Inductive builtin : list type0 -> type0 -> Type :=
  | BI_external :  forall (s : signature), builtin (args s) (res s)
  | BI_andb : builtin (B :: B :: nil)  B
  | BI_orb  : builtin (B :: B :: nil)  B
  | BI_xorb : builtin (B :: B :: nil)  B
  | BI_negb : builtin (B  :: nil)  B

  (* "type-classes" *)
  | BI_eq   : forall t, builtin (t :: t :: nil) B
  | BI_lt   : forall t, builtin (t :: t :: nil) B

  (* integer operations *)
  | BI_plus  : forall n, builtin (W n :: W n :: nil) (W n)
  | BI_minus : forall n, builtin (W n :: W n :: nil) (W n). 
  
  Section expr. 
    (* Environement is the same in the whole expr *)
    Context {E : list type2}.
    
    Inductive expr1 : type1 -> Type :=
    | Eprim : forall args res (f : builtin args res), expr0_vector args -> expr1 (T01 res) 
    | Econstant : forall (c : constant), expr1 (T01 (cst_ty c))
    (* get a register of level 1 *)
    | Eget : forall t (v : var E (Treg t)), expr1 (t)
    (* TODO: Use Tenum instead of Tint *)
    | Eget_regfile : forall size t (v : var E  (Tregfile size t)) n, expr1 (T01 (Tint n)) -> expr1 t
    | Efirst : forall t (v : var E (Tfifo t)), expr1 t
    | Eisfull : forall t (v : var E (Tfifo t)), expr1 (T01 Tbool)
    | Eisempty : forall t (v : var E (Tfifo t)), expr1 (T01 Tbool)

    | Eunion : forall {id fl} (case : expr1_disjunct fl), expr1 (Tunion id fl)
    | Etuple : forall l (v : expr1_vector l), expr1 (Ttuple l)
     with expr1_disjunct : type1_id_list -> Type :=
    | expr1_disjunct_hd:forall id t q, expr1 t -> expr1_disjunct (type1_id_list_cons id t q) 
    | expr1_disjunct_tl:forall id t q, expr1_disjunct q -> expr1_disjunct (type1_id_list_cons id t q) 

     with expr1_vector : list type1 -> Type :=
    | expr1_vector_nil: expr1_vector nil
    | expr1_vector_cons: forall t q, expr1 t -> expr1_vector q -> expr1_vector (t::q)

     with expr0_vector : list type0 -> Type :=
    | expr0_vector_nil: expr0_vector nil
    | expr0_vector_cons: forall t q, expr1 (T01 t) -> expr0_vector q -> expr0_vector (t::q). 

    Inductive expr2 : type2 -> Type :=
    | Eset : forall t , expr1 t ->  expr2 (Treg t)
    | Eset_regfile : forall size t n,
                     expr1 (T01 (Tint n)) -> expr1 t -> expr2 (Tregfile size t) 
    (* operations on fifos *)
    | Epush : forall t, expr1 t -> expr2 (Tfifo t)
    | Epop  : forall t, expr2 (Tfifo t) (* forgets the first element *)
    | Epushpop : forall t, expr1 t -> expr2 (Tfifo t)
    | Eclear : forall t, expr2 (Tfifo t)
    
    (* do nothing *)
    | Enop : forall t, expr2 t.

    Definition eval_type_sum fl := eval_type1_id_list (sum) fl. 
    
    (* applies a binary function to two arguments *)
    Definition bin_op {a b c} (f : eval_type0 a -> eval_type0 b -> eval_type0 c) 
                      : eval_type0_list (a :: b :: nil) -> eval_type0 c :=
      fun X => match X with (x,(y, _)) => f x y end. 

    (* applies a unary function to one arguments *)
    Definition un_op {a b} (f : eval_type0 a -> eval_type0 b) 
                     : eval_type0_list (a :: nil) -> eval_type0 b :=
      fun X => match X with (x,_) => f x end. 

    (* denotation of the builtin functions *)
    Definition builtin_denotation (dom : list type0) ran (f : builtin dom ran) : 
      eval_type0_list dom -> eval_type0 ran :=
      match f with
        | BI_external s => value s
        | BI_andb => @bin_op B B B andb
        | BI_orb =>  @bin_op B B B orb
        | BI_xorb => @bin_op B B B xorb
        | BI_negb =>  @un_op B B negb
        | BI_eq t => @bin_op t t B (type0_eq t)
        | BI_lt t => @bin_op t t B (type0_lt t)
        | BI_plus n => @bin_op (W n) (W n) (W n) (@Word.add n)
        | BI_minus n => @bin_op (W n) (W n) (W n) (@Word.minus n)
      end. 
    
    Fixpoint unlift (l : list type0) {struct l} : eval_type2_list (lift l) -> eval_type0_list l :=
      match l with 
          nil => fun X : eval_type2_list (lift nil) => X
        | cons t q =>  
            fun X : eval_type2_list (lift (t :: q)) => 
              (let (a, b) := X in (a, unlift q b)):eval_type0_list (t :: q)
      end.              

    Fixpoint lifter (l : list type0) r  : 
                      (eval_type0_list l -> eval_type0 r) ->
                      eval_type2_list (lift l) -> eval_type2 (Treg (T01 r)) :=
      match l with 
        | nil => fun f x => f x 
        | cons t q =>  fun f x => 
                        (let (e, e0) := x in f (e, unlift q e0):eval_type0 r):eval_type0 r
      end. 


    Variable ENV : eval_env (eval_type2) E.     


    Definition eval_type0_list := eval_env  eval_type0. 
    Definition eval_type1_list := eval_env  eval_type1. 
    Fixpoint eval_expr1 t (e : expr1 t) {struct e} : option (eval_type1 t) :=
      match  e with
        | Eprim domain range f args => 
            let eval_sexpr_vector :=
                fix eval_sexpr_vector l (v :expr0_vector l) {struct v} :  option (eval_type0_list l) :=
                match v with
                  | expr0_vector_nil => Some tt
                  | expr0_vector_cons t q e vq => 
                      do l <- eval_expr1 (T01 t) e;
                      do r <- eval_sexpr_vector q vq;
                      Some (l,r)
                end
            in 
              do args <-  (eval_sexpr_vector _ args); 
             Some (builtin_denotation _ range f args): option (eval_type1 (T01 range))

        | Econstant c => Some (cst_val (c))
        | Eunion id fl x =>
            let eval_union := 
                fix eval_union fl (e : expr1_disjunct fl) : option (eval_type_sum fl) :=
                match e with
                  | expr1_disjunct_hd id t q ex => 
                      do e <- (eval_expr1  t ex);
                      Some (inl e)
                  | expr1_disjunct_tl id t q exd => 
                      do e <- (eval_union q exd);
                      Some (inr e)
                end
            in
            eval_union fl x 
        | Etuple l v => 
            let eval_tuple := 
                fix eval_tuple fl (v : expr1_vector fl) : option(eval_type1_list fl) :=
                match v with 
                  | expr1_vector_nil => Some tt
                  | expr1_vector_cons t q e vq => 
                      do l <- eval_expr1 t e;
                      do r <- eval_tuple q vq;
                      Some (l,r)
                end
          in 
            eval_tuple l v
        | Eget t v => Some (get E (Treg t) v ENV)
        | Eget_regfile size t v n adr => 
            let rf := get E (Tregfile size t) v ENV in 
            do adr <- eval_expr1 _ adr; 
              Regfile.get size _ rf  (Word.val adr)
        | Efirst t v => 
            let f := get E (Tfifo t) v ENV in
            FIFO.first _ f 
        | Eisfull t v => 
            let f := get E (Tfifo t) v ENV in
            Some (FIFO.isfull _ f) 

        | Eisempty t v => 
            let f := get E (Tfifo t) v ENV in
            Some (FIFO.isempty _ f) 
      end. 
        
    Fixpoint eval_expr2 t (e : expr2 t) {struct e} : option (eval_type2 t) :=
      match e with
        | Eset t x => eval_expr1 t x 
        | Eset_regfile size t n x x0 => admit
        | Epush t x => admit
        | Epop t => admit
        | Epushpop t x => admit
        | Eclear t => admit
        | Enop t => admit        (* should be a var *)
      end. 

    (* Fixpoint eval_tuple fl (v : expr_vector fl) : eval_type2_list fl := *)
    (*   match v with  *)
    (*     | expr_vector_nil => tt *)
    (*     | expr_vector_cons t q e vq => (eval_expr t e, eval_tuple q vq) *)
    (*   end.  *)
    
    (* Fixpoint eval_expr_vector l (v : expr_vector l) {struct v} :  eval_type2_list l := *)
    (*   match v with *)
    (*     | expr_vector_nil => tt *)
    (*     | expr_vector_cons t q e vq => (eval_expr t e, eval_expr_vector q vq) *)
    (*   end.  *)
    
    (* Fixpoint eval_union fl (e : expr_disjunct fl) : eval_type_sum fl := *)
    (*   match e with *)
    (*     | expr_disjunct_hd id t q ex => inl (eval_expr  t ex) *)
    (*     | expr_disjunct_tl id t q exd => inr (eval_union q exd) *)
    (*   end.  *)
  End expr. 

  Section pattern.  

    (* A pattern [p] of type [pattern E ty] has free variables in E and has type [ty].*)
    
    Inductive pattern1 : list type2 -> type1 -> Type  :=
    | Pvar1 : forall t, pattern1 (cons (Treg t) nil) t
    | Phole1 : forall t, pattern1 nil t
    | Pconstant : forall (c : constant), pattern1 nil (T01 (cst_ty c))
    | Punion : forall E id fl (x : pattern1_disjunct E fl), pattern1 E (Tunion id fl)
    | Ptuple : forall E l, pattern1_vector E l -> pattern1 E (Ttuple l)
    with pattern1_disjunct : list type2  -> type1_id_list -> Type :=
(* | pattern_disjunct_nil :  pattern_disjunct anil  *)
    | pattern1_disjunct_hd  : forall E id t q, pattern1 E t -> pattern1_disjunct E (type1_id_list_cons id t q) 
    | pattern1_disjunct_tl  : forall E id t q, pattern1_disjunct E q -> pattern1_disjunct E (type1_id_list_cons id t q)
    with pattern1_vector : list type2  -> list type1 -> Type :=
    | pattern_vector_nil : pattern1_vector nil nil 
    | pattern_vector_cons : forall E F t q, pattern1 E t -> pattern1_vector F q -> pattern1_vector (List.app E F)(t::q). 

    Inductive pattern2 : list type2 -> type2 -> Type :=
    | Pvar2 : forall t, pattern2 (cons t nil) t (* bind a fifo, a regfile or a register *)
    | Phole2 : forall t, pattern2 (nil) t       (* bind nothing *)
    | Plift : forall E t, pattern1 E t -> pattern2 E (Treg t) . (* actual binders *)
      
              
    Fixpoint pattern1_match E t (p : pattern1 E t) : eval_type1 t -> option (eval_env eval_type2  E) :=
      match p with
        | Pvar1 t => fun x => Some (x,tt)
        | Phole1 t => fun _ => Some tt
        | Pconstant c => fun _ => Some tt (* TODO should fail sometimes *)
        | Punion E id fl x => pattern1_match_disjunct E fl x
        | Ptuple E l x => pattern1_match_vector E l x
      end
with 
    pattern1_match_vector (E: list type2) l (pv : pattern1_vector E l) : eval_type1_list l -> option (eval_env eval_type2 E) :=
    match pv with 
      | pattern_vector_nil => fun _ => (Some tt): option (eval_env eval_type2 nil)
      | pattern_vector_cons  E F t q pEt pvFq => 
          fun V =>
            (do X <- (pattern1_match E t pEt (fst V));
             do Y <- (pattern1_match_vector F q pvFq (snd V));
             Some (append_envs _ _ X Y))
    end
     with 
         pattern1_match_disjunct E fl (pl : pattern1_disjunct E fl) : 
         eval_type_sum fl -> option (eval_env  eval_type2  E) :=
         match pl with
           | pattern1_disjunct_hd E id t q pEt  =>  
               fun X => match X with inl X => pattern1_match E t pEt X | _ => None end
           | pattern1_disjunct_tl E id t q pdEq =>  
               fun X => match X with inr X => pattern1_match_disjunct E q pdEq X | _ => None end
         end. 
         
         Fixpoint pattern2_match E t (p : pattern2 E t) : eval_type2 t -> option (eval_env eval_type2 E) :=
      match p with
        | Pvar2 t => fun x => Some (x,tt)
        | Phole2 t => fun _ => Some tt
        | Plift E t p => pattern1_match E t p
      end. 
            
  End pattern. 

  (* [pattern2_vector E F] binds [F] in the memory [E]  *)
  Inductive pattern2_vector : list type2  -> list type2 -> Type :=
    | pattern2_vector_nil : pattern2_vector nil nil 
    | pattern2_vector_cons : forall E F t q, 
                               pattern2 E t -> pattern2_vector q F -> 
                               pattern2_vector (t::q) (List.app E F). 

  Inductive expr2_vector (E : list type2) : list type2 -> Type :=
  | expr2_vector_nil : expr2_vector E nil
  | expr2_vector_cons : forall t q, @expr2 E t -> expr2_vector E q -> expr2_vector E (cons t q). 


  (* [where_clause E F] : starting with bindings [E], produce bindings
  [F] such that [E] ⊂ [F] *)

  Inductive where_clause : list type2 ->  list type2  -> Type :=
  | where_clause_nil : forall E, where_clause E E
  | where_clause_cons : 
    forall E F G t, pattern1 F t  -> @expr1 E t -> 
               where_clause (List.app E F) G ->
               where_clause E G. 
                  
  Record rule mem :=
    mk_rule 
      {
        env1 : list type2; 
        env2 : list type2;
        lhs : @pattern2_vector mem env1;
        where_clauses : where_clause env1 env2;
        cond: @expr1 env2 (T01 Tbool);
        rhs : @expr2_vector env2 mem
      }.
  
  Arguments env1 {mem} r. 
  Arguments env2 {mem} r. 
  Arguments lhs {mem} r. 
  Arguments cond {mem} r. 
  Arguments rhs {mem} r. 
  
  Record TRS :=
    {
      trs_type : list type2;
      trs_rules : list (rule trs_type) 
    }. 
  
  Definition relation A := A -> A -> Prop. 
  Definition union {A} (R S : relation A) := fun x y => R x y \/ S x y. 
  
  Fixpoint pattern2_vector_match E F (P : pattern2_vector E F ) : 
    eval_type2_list E -> option (eval_env eval_type2 F) :=
    match P with 
      | pattern2_vector_nil => fun _ => Some tt
      | pattern2_vector_cons E F t q p2Et p2vFq =>
          fun X => 
            let (A, B) := X in
              do X <- pattern2_match E t p2Et A;
              do Y <- pattern2_vector_match _ _ p2vFq B;
              Some (append_envs _ _  X Y)
    end. 
  
  Fixpoint where_clause_match {E F} (W : where_clause E F) {struct W}: 
    eval_type2_list E -> option (eval_type2_list F) :=
    match W with 
      | where_clause_nil _ => fun X => Some X
      | where_clause_cons E F G t pat exp w =>
          fun x =>
            do e <- eval_expr1 x t exp;
            do B <- pattern1_match F t pat e;
            where_clause_match w (append_envs _ _ x B  )
    end. 

  Definition eval_expr2_vector t env (v : @expr2_vector env t) : 
    eval_type2_list env -> option (eval_type2_list t) . 
  induction v. 
  simpl. intros; auto.  constructor. auto. apply tt. 
  simpl. intros . 
  refine (do a <- eval_expr2 X _ e; _). 
  refine (do b <- IHv X; _).
  refine (Some (a,b)). 
  Defined. 

  Definition eval_rule tyl (r : rule tyl) : relation (eval_type2_list (tyl)) :=
    fun M1 M2 => 
      exists E, exists F,  (pattern2_vector_match _ _ (lhs r) M1 = Some E
           /\ where_clause_match (where_clauses _ r) E = Some F
           /\ eval_expr1 F _ (cond r) = Some true
           /\ eval_expr2_vector _ _ (rhs r) F = Some M2). 
  
  Fixpoint eval_rules ty (l : list (rule ty)) : relation (eval_type2_list (ty)) :=
    match l with
      | nil => fun _ _ => True
      | cons t q => union (eval_rule ty t) (eval_rules ty q)
    end. 
  
  Definition eval_TRS T := eval_rules _ (trs_rules T). 
  
  Definition run_rule ty (r : rule ty) : eval_type2_list ty -> option (eval_type2_list ty) :=
    fun M1 => 
      do E <- pattern2_vector_match _ _ (lhs  r) M1;
      do F <- where_clause_match (where_clauses _ r) E;

      if (@eval_expr1 (env2  r) F _ (cond  r))
      then (@eval_expr2_vector _ _  (rhs  r) F)
      else None . 
  
  
  Fixpoint iter_option {A} n (f : A -> option A) x :=
    match n with 
      | 0 => Some x
      | S n => match f x with | None => Some x | Some x => iter_option n f x end 
    end. 
  
  Fixpoint first_rule {ty} (l : list (rule ty)) x :=
    match l with 
      | nil => Some x
      | cons t q => 
          match run_rule _ t x with 
            | None => first_rule q x
            | Some x => Some x 
          end
    end. 

  Fixpoint run_unfair n T x :=
    match n with 
      | 0 => Some x
    | S n => 
        match first_rule (trs_rules T) x with 
          | None => Some x
          | Some x => run_unfair n T x
        end
  end. 

  Notation "[]" := nil.
  Notation "a :: b" := (cons a b). 
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
  Open Scope string_scope.
  
  Delimit Scope expr_scope with expr. 
  Notation "[| x , .. , z |]"  :=  (Etuple _ (expr1_vector_cons _ _ x .. (expr1_vector_cons _ _ z expr1_vector_nil ).. )) (at level  0): expr_scope.


  Notation "{< f ; x ; y >}" := (Eprim _ _ (f) (expr0_vector_cons _ _ x (expr0_vector_cons _ _ y expr0_vector_nil))).

  Notation "a || b" := ({< BI_orb ; a ; b >}) : expr_scope. 
  Notation "a - b" := ({< BI_minus _ ; a ; b >}) : expr_scope. 
  Notation "a + b" := ({< BI_plus _ ; a ; b >}) : expr_scope. 
  Notation "a = b" := ({< BI_eq _ ; a ; b >}) : expr_scope. 
  Notation "a < b" := ({< BI_lt _ ; a ; b >}) : expr_scope. 
  Notation "x <= y" := ((x < y) || (x = y))%expr : expr_scope. 
  Notation "! x" := (Eget _ x) (at level  10) : expr_scope . 
  Notation "[| x |]"  :=  (Etuple _ (expr1_vector_cons _ _ x expr1_vector_nil )) (at level  0): expr_scope.  
  Notation "{< x >}" := (Econstant x): expr_scope. 
  
  Delimit Scope pattern_scope with pattern.    
  Notation "[| x , .. , z |]" := (Ptuple _ _ (pattern_vector_cons _ _ _ _ x .. (pattern_vector_cons _ _ _ _ z pattern_vector_nil ).. )) (at  level 0): pattern_scope.  
  
  Notation "X 'of' u :: q " := (type1_id_list_cons  X u q) (at level 60, u at next level,  right associativity). 

  (* Notations for expr2 *)
  Delimit Scope expr2_scope with expr2. 
  Arguments Eset_regfile {E} size t n _%expr _%expr.  

  Notation "[| x , .. , z |]"  :=  ((expr2_vector_cons _ _ _ x .. (expr2_vector_cons _ _ _ z (expr2_vector_nil _) ).. )) (at level  0): expr2_scope.
  Notation "'[' key '<-' v ']' " := ( Eset_regfile _ _ _  key v )(at level 0, no associativity) : expr2_scope.
  Notation "•" := (Enop _) : expr2_scope. 
  
  Definition mk_rule' {mem} env pat cond expr : rule mem :=
    mk_rule mem env env pat (where_clause_nil _ ) cond expr. 

  Module Mod. 
  
    Definition Num : type1 := T01 (Tint 32). 
    Definition Val : type1 :=
      Tunion "Val" ("MOD" of (Ttuple [Num; Num]) 
                          :: "VAL" of (Ttuple [Num]) 
                 :: type1_id_list_nil ). 
    
    Definition mod_iterate_rule : rule [Treg Val]. 
    set (env := [Treg Num; Treg Num]). 
    set (a := var_0 : var env (Treg Num)). 
    set (b := var_S var_0 : var env (Treg Num)). 
    apply (mk_rule' env). 

    Definition pattern2_vector_singleton E t x :=
      pattern2_vector_cons E _ t _ x pattern2_vector_nil. 
    apply (pattern2_vector_singleton env). 
    apply Plift. 
    eapply Punion.  apply  (pattern1_disjunct_hd). 
    apply ([| Pvar1 Num, Pvar1 Num |])%pattern. 
    
    apply (! b <= ! a)%expr. 

    Definition expr2_vector_singleton E t x :=
      expr2_vector_cons E t _ x (expr2_vector_nil _). 
    apply expr2_vector_singleton. 
    eapply Eset. eapply Eunion. eapply expr1_disjunct_hd.  apply ([| !a - !b, !b|])%expr. 
    Defined. 

    Definition mod_done_rule : rule [Treg Val]. 
    set (env := [Treg Num; Treg Num]). 
    set (a := var_0 : var env (Treg Num)). 
    set (b := var_S var_0 : var env (Treg Num)). 
    apply (mk_rule' env). 
    
    apply (pattern2_vector_singleton env). 
    apply Plift. eapply Punion. apply pattern1_disjunct_hd. 
    apply ([| Pvar1 Num, Pvar1 Num |])%pattern. 
    
    apply (!a < !b)%expr. 
    
    apply expr2_vector_singleton. 
    apply Eset. 
    apply Eunion. apply expr1_disjunct_tl. apply expr1_disjunct_hd.
    apply ([| !a |])%expr. 
    Defined. 
    
    Definition TRS : TRS :=
      {| trs_type := [Treg Val]; 
         trs_rules := [mod_iterate_rule; mod_done_rule ]|}. 
    
    Definition AA : Word.T 32 := Word.repr 32 31. 
    Definition BB : Word.T 32 := Word.repr 32 3. 
    
    Definition this_ENV : eval_env eval_type2 [Treg Num; Treg Num] := (AA, (BB, tt)). 
    
    Eval compute in run_unfair 10 TRS ((inl this_ENV, tt)). 
    
  End Mod. 

  Module PROC. 
    Definition val := T01 (Tint 16).
    
    Definition reg :=  T01 (Tint 2).  (* todo : should define an enum type *)
    Definition RF := Tregfile 4 (val). 
    Definition instr : type1 := 
      Tunion "instr" ("ILOAD"  of (Ttuple [reg ;val]) 
                   :: "LOADPC" of (reg) 
                   :: "ADD" of (Ttuple [reg;reg;reg]) 
                   :: "BZ" of (Ttuple [reg;reg])
                   :: "LOAD" of (Ttuple [reg;reg])
                   :: "STORE" of (Ttuple [reg;reg])
                   :: type1_id_list_nil ). 

    Definition IMEM := Tregfile (two_power_nat 16) instr. 
    Definition DMEM := Tregfile (two_power_nat 16) val. 
    Definition PC := Treg val. 
    Definition state := [PC; RF; IMEM; DMEM]. 
    Definition loadi_rule : rule state. 
    set (env1 := state). 
    set (env2 := List.app state  [Treg reg; Treg val]). 
    set (pc := var_0 : var env1 PC). 
    set (rf := var_S var_0 : var env1 RF). 
    set (imem := var_S (var_S var_0) : var env1 IMEM). 
    set (dmem := var_S (var_S (var_S var_0)) : var env1 DMEM). 
    set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
    set (const := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg val)). 
    apply (mk_rule state env1 env2). 
    Definition trivial_pattern2_vector l : pattern2_vector l l.
    induction l. 
    constructor. 
    apply (pattern2_vector_cons [a] l a l). constructor.  
    apply IHl. 
    Defined. 
    apply trivial_pattern2_vector. 
    eapply where_clause_cons. 
    apply Punion. apply pattern1_disjunct_hd. 
    apply ([| Pvar1 reg, Pvar1 val  |])%pattern. 
    eapply Eget_regfile. 
    apply imem. 
    apply (Eget _ pc). 
    apply where_clause_nil. 

    apply ({< Cbool true >})%expr. 
    

    
    Definition var_lift : forall T E F, forall t, @var T E t -> @var T (E++F) t.  Admitted. 
    refine ([| Eset _ (! (var_lift _ _ _ _ pc )+ {< Cword 1>})%expr , [!rd <- !const] , • , • |])%expr2. 
    Defined. 
  End PROC. 
End BS. 
  
Module ATS. 
  Inductive type :=
  | Tregfile : forall (size : Z) (base : type0) , type
  | Tfifo : type0 -> type
  | Tbase : type0 -> type
  | Tinput  : type0 -> type
  | Toutput : type0 -> type. 
         
                  
  Fixpoint eval_type (t : type) : Type :=
    match t with
      | Tregfile size bt => Regfile.T size (eval_type0 bt)
      | Tfifo bt => FIFO.T (eval_type0 bt)
      | Tbase bt => eval_type0 bt
      | Tinput bt => eval_type0 bt
      | Toutput bt => eval_type0 bt
    end. 

  Definition eval_list_type := eval_env eval_type. 
  
  
  Section expr. 
    Variable Env : list type. 
    
    Inductive expr : type0 -> Type :=
    | Eprim : forall f (args: expr_vector (args (f))), expr ( (res (f)))
    | Eget : forall t (v : var Env (Tbase t)), expr t
    (* operations on arrays *)
    | Eget_array : forall size  n t (v : var Env (Tregfile size t)), expr (Tint n) -> expr t
    (* operations on fifo *)
    | Efirst : forall t (v : var Env (Tfifo t)), expr t
    | Eisfull : forall t (v : var Env (Tfifo t)), expr (Tbool)
    | Eisempty : forall t (v : var Env (Tfifo t)), expr (Tbool)
    (* operations on Inputs *)
    | Eget_input : forall t (v : var Env (Tinput t)), expr t
    (* operations on Outputs *)
    | Eget_output : forall t (v : var Env (Toutput t)), expr t

    with expr_vector : list type0 -> Type :=
    | expr_vector_nil : expr_vector nil
    | expr_vector_cons : forall t q, expr  (t) -> expr_vector q -> expr_vector (t::q). 

    (* top level expressions *)
    Inductive expr2 : type -> Type :=
    | Eset : forall t , expr t ->  expr2 (Tbase t)
    | Eset_array : forall size n t,
                     expr (Tint n) -> expr t -> expr2 (Tregfile size t)
    (* operations on fifos *)
    | Epush : forall t, expr t -> expr2 (Tfifo t)
    | Epop  : forall t, expr2 (Tfifo t) (* forgets the first element *)
    | Epushpop : forall t, expr t -> expr2 (Tfifo t)
    | Eclear : forall t, expr2 (Tfifo t)
                          
    (* set an output *)
    | Eset_output : forall t,  expr t -> expr2 (Toutput t)
    
    (* do nothing *)
    | Enop : forall t, expr2 t.
 

    Variable ENV : eval_list_type Env. 

    Fixpoint  eval_expr t (e : expr t) : option (eval_type0 t) :=
      match e with
        | Eprim f args => 
            let eval_expr_vector :=
                fix eval_expr_vector l (v : expr_vector l) {struct v} :  option (eval_type0_list l) :=
                match v with
                  | expr_vector_nil => Some tt
                  | expr_vector_cons hd q e vq => 
                      do hd <- eval_expr hd e; 
                      do tl <- eval_expr_vector q vq;
                      Some (hd,tl)
                end
            in 
              do args <-  (eval_expr_vector _ args);
            Some (value (f) args)
        | Eget t v => Some (get Env (Tbase t) v ENV)
        | Efirst bt fifo => 
            let fifo := (get Env (Tfifo bt) fifo ENV ) in
              FIFO.first (eval_type0 bt)  fifo 
        | Eisfull bt fifo => 
            let fifo := (get Env (Tfifo bt) fifo ENV ) in 
              Some (FIFO.isfull _ fifo)
        | Eisempty bt fifo => 
            let fifo := (get  Env (Tfifo bt) fifo ENV ) in 
              Some  (FIFO.isempty _ fifo)
        | Eget_input bt x => 
            let x := get  Env (Tinput bt) x ENV in 
              Some x
        | Eget_output bt x => 
            let x := get  Env (Toutput bt) x ENV in 
              Some x
        | Eget_array size n bt v idx  => 
            let v := get  Env (Tregfile size bt) v ENV in 
              do idx <- eval_expr _ idx;
              Regfile.get size _ v (Word.val idx)
        end. 
  Definition admit {t} : t .  Admitted. 
  Fixpoint eval_expr2 t (e : expr2 t) : eval_type t ->  option (eval_type t) :=
    match e with
      | Eset t e => 
          fun r => eval_expr t e
      | Eset_array size n t eid e =>
      fun v => 
        do eid <- eval_expr _ eid;
        do e <- eval_expr _ e;
        @Regfile.set size (eval_type0 t) v (Word.val eid) e
      | Epush t e => 
          fun f =>
            do e <- eval_expr t e;
          Some (FIFO.push _ e f)
  
      | Epop t => 
      fun f => 
        FIFO.pop _ f 
      | Epushpop t e => 
          fun f => 
            do f <- FIFO.pop _ f;    (* UNDEFINED *)
            do e <- eval_expr t e;
            Some (FIFO.push _ e f)
      | Eclear t =>
          fun f => Some (FIFO.clear _ f)
      | Eset_output t e => 
          fun _ => eval_expr t e
      | Enop t => fun x => Some x
    end. 
End expr. 



(* A transition is parametrized by a memory environment. 
   It contains a guard (a boolean expression), and a dependtly-typed list, which ensure that every memory location is updated.  *)

Record transition Env :=
  { pi : expr Env Tbool;
    alpha : dlist type (expr2 Env) Env}.
                    
Definition eval_alpha E (alpha : dlist type (expr2 E) E) :
  eval_list_type E -> option (eval_list_type E) :=
  fun  (X : eval_list_type E) =>
    dlist_fold type (expr2 E) eval_type (eval_expr2 E X) E alpha X.

Record ATS :=
  {
    memory : list type;
    transitions : list (transition (memory))
  }. 

Definition eval_transition (mem: list type) (tr : transition mem) : 
  eval_list_type mem -> option (eval_list_type mem) :=
  fun (E : eval_list_type mem) =>
    let guard := eval_expr mem E Tbool (pi mem tr) in
      match guard with
        | Some true => eval_alpha mem (alpha mem tr) E
        | Some false => None
        | None => None
      end.

Fixpoint eval_transitions mem (l : list (transition mem))  :=
  match l with 
    | nil => fun _ _  => True
    | cons t q => BS.union (fun x y => eval_transition mem t x = Some y) 
                       (eval_transitions mem q)
  end. 
  
Definition eval (X : ATS) :=
  eval_transitions (memory X) (transitions X). 

End ATS. 


Module RTL. 
  Inductive type :=
  | Tregfile : forall (size : Z) (base : type0) , type
  | Tfifo : type0 -> type
  | Tbase : type0 -> type
  | Tinput  : type0 -> type
  | Toutput : type0 -> type. 

  Fixpoint eval_type (t : type) : Type :=
    match t with
      | Tregfile size bt =>Regfile.T size (eval_type0 bt) 
      | Tfifo bt => FIFO.T (eval_type0 bt)
      | Tbase bt => eval_type0 bt
      | Tinput bt => eval_type0 bt
      | Toutput bt => eval_type0 bt
    end. 

  Variable Env : list type. 
    
  Inductive expr : type0 -> Type :=
  | Eprim : forall f (args: expr_vector (args (f))), expr ( (res ( f)))
  | Eget : forall t (v : var Env (Tbase t)), expr t
  (* operations on arrays *)
  | Eget_array : forall size  n t (v : var Env (Tregfile size t)), expr (Tint n) -> expr t
  (* operations on fifo *)
  | Efirst : forall t (v : var Env (Tfifo t)), expr t
  | Eisfull : forall t (v : var Env (Tfifo t)), expr (Tbool)
  | Eisempty : forall t (v : var Env (Tfifo t)), expr (Tbool)
  (* operations on Inputs *)
  | Eget_input : forall t (v : var Env (Tinput t)), expr t
  (* operations on Outputs *)
  | Eget_output : forall t (v : var Env (Toutput t)), expr t
   with expr_vector : list type0 -> Type :=
  | expr_vector_nil : expr_vector nil
  | expr_vector_cons : forall t q, expr  (t) -> expr_vector q -> expr_vector (t::q). 


  Record reg_update (t : type0): Type :=
    {
      latch_enable : expr Tbool;
      data : expr t
    }. 
  
  Record array_update (size : Z) (width : nat) (t : type0) :=
    {
      write_addr : expr (Tint width);
      write_data : expr t;
      write_enable : expr Tbool
    }.

  Record fifo_update (t : type0) :=
    {
      enqueue_data : expr t;
      enqueue_enable : expr Tbool;
      dequeue_enable : expr Tbool;
      clear_enable : expr Tbool
    }. 
  
  Inductive expr2 : type -> Type :=
  (* expression to affect and latch enable  *)
  | Eregister : forall t, reg_update t -> expr2 (Tbase t)
  (* array operations *)
  | Earray :  forall size width t, array_update size width t -> 
                   expr2 (Tregfile size t)
  (* fifo operations *)
  | Efifo : forall t, fifo_update t ->  expr2 (Tfifo t) 
  | Enop : forall t, expr2 t. 
              
  
End RTL. 

(*     (global-set-key '[(f5)]          'proof-assert-next-command-interactive) 
 *) 
