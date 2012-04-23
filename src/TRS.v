Require Import Common. 

Inductive type1 : Type :=
  | T01 : type0 -> type1
  | Tunion : forall (idx : ident), list (ident * type1) -> type1
  | Ttuple : list type1 -> type1.

Inductive type2 :=
  | Treg : type1 -> type2
  | Tregfile  : nat -> type1 -> type2
  | Tfifo : nat -> type1 -> type2
  | Tinput : type1 -> type2
  | Toutput : type1 -> type2. 

(** [eval_type t] computes the coq denotation of the [type] [t] *)
Fixpoint eval_type1  (t : type1 ) : Type :=
  match t with
    | T01 st => eval_type0 st 
    | Tunion  _ cases => List.fold_right (fun x acc => eval_type1 (snd x) + acc)%type unit cases
    | Ttuple  x =>  eval_env eval_type1 x
  end. 

Definition eval_type2 (t : type2) : Type :=
  match t with 
      Treg t => eval_type1 t
    | Tregfile n b => Regfile.T n (eval_type1 b)
    | Tfifo n st => FIFO.T n (eval_type1 st)
    | Tinput t => eval_type1 t
    | Toutput t => eval_type1 t
  end. 

Definition eval_type2_list  l := eval_env  eval_type2 l. 

Notation "x :: q" := (cons  x q). 
Definition T02 x := Treg (T01 x). 

Definition lift := List.map T02. 

Section expr. 
  (* Environement is the same in the whole expr *)
  Variable (E : list type2).
  
  Inductive expr1 : type1 -> Type :=
  | Eprim : forall args res (f : builtin args res), dlist  (fun t => expr1 (T01 t)) args -> expr1 (T01 res) 
  | Econstant : forall (c : constant), expr1 (T01 (cst_ty c))
  (* get a register of level 1 *)
  | Eget : forall t (v : var E (Treg t)), expr1 (t)
  (* get for input/output  *)
  | Eget_input  : forall t (v : var E (Tinput t)), expr1 (t)
  | Eget_output : forall t (v : var E (Toutput t)), expr1 (t)
                                                     
  (* TODO: Use Tenum instead of Tint *)
  | Eget_regfile : forall size t (v : var E  (Tregfile size t)) n, expr1 (T01 (Tint n)) -> expr1 t
  | Efirst : forall n t (v : var E (Tfifo n t)), expr1 t
  | Eisfull : forall n t (v : var E (Tfifo n t)), expr1 (T01 Tbool)
  | Eisempty : forall n t (v : var E (Tfifo n t)), expr1 (T01 Tbool)
                                                    
  | Eunion : forall {id fl} (case : expr1_disjunct fl), expr1 (Tunion id fl)
  | Etuple : forall l (v : dlist expr1 l), expr1 (Ttuple l)
                                            with expr1_disjunct : list (ident * type1) -> Type :=
  | expr1_disjunct_hd:forall id t q, expr1 t -> expr1_disjunct ((id,t) :: q) 
  | expr1_disjunct_tl:forall id t q, expr1_disjunct q -> expr1_disjunct ((id,t)::q) 
                                            with expr1_vector : list type1 -> Type :=
  | expr1_vector_nil: expr1_vector nil
  | expr1_vector_cons: forall t q, expr1 t -> expr1_vector q -> expr1_vector (t::q). 

  Inductive expr2 : type2 -> Type :=
  | Eset : forall t , expr1 t ->  expr2 (Treg t)
  | Eset_regfile : forall size t n,
                     expr1 (T01 (Tint n)) -> expr1 t -> expr2 (Tregfile size t) 
  (* operations on fifos *)
  | Epush : forall n t, expr1 t -> expr2 (Tfifo n t)
  | Epop  : forall n t, expr2 (Tfifo n t) (* forgets the first element *)
  | Epushpop : forall n t, expr1 t -> expr2 (Tfifo n t)
  | Eclear : forall n t, expr2 (Tfifo n t)

  (* set an output *)
  | Eset_output : forall t, expr1 t -> expr2 (Toutput t)
  (* do nothing *)
  | Enop : forall t, expr2 t.
  
  Definition eval_type_sum (fl : list (ident * type1)) := 
    List.fold_right (fun x acc => eval_type1 (snd x) + acc)%type unit fl. 
  
  
  (* Fixpoint unlift (l : list type0) {struct l} : eval_type2_list (lift l) -> eval_type0_list l := *)
  (*   match l with  *)
  (*         nil => fun X : eval_type2_list (lift nil) => X *)
  (*       | cons t q =>   *)
  (*           fun X : eval_type2_list (lift (t :: q)) =>  *)
  (*             (let (a, b) := X in (a, unlift q b)):eval_type0_list (t :: q) *)
  (*     end.               *)

  (*   Fixpoint lifter (l : list type0) r  :  *)
  (*                     (eval_type0_list l -> eval_type0 r) -> *)
  (*                     eval_type2_list (lift l) -> eval_type2 (Treg (T01 r)) := *)
  (*     match l with  *)
  (*       | nil => fun f x => f x  *)
  (*       | cons t q =>  fun f x =>  *)
  (*                       (let (e, e0) := x in f (e, unlift q e0):eval_type0 r):eval_type0 r *)
  (*     end.  *)


    Variable ENV : eval_env (eval_type2) E.     


    Definition eval_type0_list := eval_env  eval_type0. 
    Definition eval_type1_list := eval_env  eval_type1. 
    Notation expr0 := (fun t => expr1 (T01 t)). 
    Fixpoint eval_expr1 t (e : expr1 t) {struct e} : option (eval_type1 t) :=
      match  e with
        | Eprim domain range f args => 
            let eval_sexpr_vector :=
                fix eval_sexpr_vector l (v :dlist  expr0 l) {struct v} :  option (eval_type0_list l) :=
                match v with
                  | dlist_nil => Some tt
                  | dlist_cons t q e vq => 
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
                fix eval_tuple l (v : dlist expr1 l) : option(eval_type1_list l) :=
                match v with 
                  | dlist_nil => Some tt
                  | dlist_cons t q e vq => 
                      do l <- eval_expr1 t e;
                      do r <- eval_tuple q vq;
                      Some (l,r)
                end
          in 
            eval_tuple l v
        | Eget t v => Some (get E (Treg t) v ENV)
        | Eget_input t v => Some (get E (Tinput t) v ENV)
        | Eget_output t v => Some (get E (Toutput t) v ENV)
        | Eget_regfile size t v n adr => 
            let rf := get E (Tregfile size t) v ENV in 
            do adr <- eval_expr1 _ adr; 
              @Regfile.get size _ rf  (Word.unsigned adr)
        | Efirst n t v => 
            let f := get E (Tfifo n t) v ENV in
            @FIFO.first _ n f 
        | Eisfull n t v => 
            let f := get E (Tfifo n t) v ENV in
            Some (@FIFO.isfull _ n f) 

        | Eisempty n t v => 
            let f := get E (Tfifo n t) v ENV in
            Some (@FIFO.isempty _  n f) 
      end. 
        
    Fixpoint eval_expr2 t (e : expr2 t) {struct e} : eval_type2 t -> option (eval_type2 t) :=
      match e with
        | Eset t x => fun _ => eval_expr1 t x 
        | Eset_regfile size t n adr val => 
            fun old => 
              do adr <- eval_expr1 _ adr; 
              do val <- eval_expr1 t val;
              let adr := Word.unsigned adr in 
              check (lt_nat_bool adr size);
              Some (@Regfile.set size (eval_type1 t) old adr val)
        | Epush n t x => 
            fun q => 
              do x <- eval_expr1 t x;
              Some (FIFO.push x q)
        | Epop n t => 
            fun q => 
              @FIFO.pop (eval_type1 t) n q
        | Epushpop n t x => 
          fun q => 
            do f <- @FIFO.pop _ n q;    (* UNDEFINED *)
            do e <- eval_expr1 t x;
            Some (FIFO.push  e f)
        | Eclear n t => 
            fun q => 
            Some (@FIFO.clear (eval_type1 t) n q)
        | Enop t => 
            fun x => Some x
        | Eset_output t e => 
            fun _ => 
              eval_expr1 t e
      end. 

  End expr. 

  Section pattern.  

    (* A pattern [p] of type [pattern E ty] has free variables in E and has type [ty].*)
    
    Inductive pattern1 : list type2 -> type1 -> Type  :=
    | Pvar1 : forall t, pattern1 (cons (Treg t) nil) t
    | Phole1 : forall t, pattern1 nil t
    | Pconstant : forall (c : constant), pattern1 nil (T01 (cst_ty c))
    | Punion : forall E id fl (x : pattern1_disjunct E fl), pattern1 E (Tunion id fl)
    | Ptuple : forall E l, pattern1_vector E l -> pattern1 E (Ttuple l)
    with pattern1_disjunct : list type2  -> list (ident * type1) -> Type :=
(* | pattern_disjunct_nil :  pattern_disjunct anil  *)
    | pattern1_disjunct_hd  : forall E id t q, pattern1 E t -> pattern1_disjunct E ((id,t)::q) 
    | pattern1_disjunct_tl  : forall E id t q, pattern1_disjunct E q -> pattern1_disjunct E ( (id,t)::q)
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

  (* Inductive expr2_vector (E : list type2) : list type2 -> Type := *)
  (* | expr2_vector_nil : expr2_vector E nil *)
  (* | expr2_vector_cons : forall t q, @expr2 E t -> expr2_vector E q -> expr2_vector E (cons t q).  *)

  Definition expr2_vector (E : list type2) := dlist (@expr2 E). 
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
            do e <- eval_expr1 _ x t exp;
            do B <- pattern1_match F t pat e;
            where_clause_match w (append_envs _ _ x B  )
    end. 

  Definition eval_expr2_vector mem env (v : @expr2_vector env mem) : 
    eval_type2_list env -> eval_type2_list mem -> option (eval_type2_list mem) := 
    (fun ENV MEM =>  (dlist_fold _ _ _ (eval_expr2 _ ENV) mem v MEM)). 

  Definition eval_rule mem (r : rule mem) : relation (eval_type2_list mem) :=
    fun M1 M2 => 
      exists E, exists F,  (pattern2_vector_match _ _ (lhs r) M1 = Some E
           /\ where_clause_match (where_clauses _ r) E = Some F
           /\ eval_expr1 _ F _ (cond r) = Some true
           /\ eval_expr2_vector _ _ (rhs r) F M1 = Some M2). 
  
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
      then (@eval_expr2_vector _ _  (rhs  r) F M1)
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

  
  Notation "{< f ; x ; y >}" := (Eprim _ _ (f) (dlist_cons  x (dlist_cons y dlist_nil))).

  Notation "{< f ; x >}" := (Eprim _ _ (f) (dlist_cons x dlist_nil)).

  Notation "~ x" :=  ({< BI_negb ; x >}) : expr_scope. 
  Notation "a || b" := ({< BI_orb ; a ; b >}) : expr_scope. 
  Notation "a - b" := ({< BI_minus _ ; a ; b >}) : expr_scope. 
  Notation "a + b" := ({< BI_plus _ ; a ; b >}) : expr_scope. 
  Notation "a = b" := ({< BI_eq _ ; a ; b >}) : expr_scope. 
  Notation "a < b" := ({< BI_lt _ ; a ; b >}) : expr_scope. 
  Notation "x <= y" := ((x < y) || (x = y))%expr : expr_scope. 
  Notation "x <> y" := (~(x = y))%expr : expr_scope. 
  Notation "! x" := (Eget _ x) (at level  10) : expr_scope . 
  Notation "[| x |]"  :=  (Etuple _ (expr1_vector_cons _ _ x expr1_vector_nil )) (at level  0): expr_scope.  
  Notation "{< x >}" := (Econstant x): expr_scope. 
  
  Delimit Scope pattern_scope with pattern.    
  Notation "[| x , .. , z |]" := (Ptuple _ _ (pattern_vector_cons _ _ _ _ x .. (pattern_vector_cons _ _ _ _ z pattern_vector_nil ).. )) (at  level 0): pattern_scope.  
  
  Notation "X 'of' u :: q " := ((X,u)::q) (at level 60, u at next level,  right associativity). 

  (* Notations for expr2 *)
  Delimit Scope expr2_scope with expr2. 
  Arguments Eset_regfile {E} size t n _%expr _%expr.  

  Arguments dlist_cons {T P} t q _ _ . 
  Arguments dlist_nil {T P}. 
  Notation "[| x , .. , z |]"  :=  ((dlist_cons  _ _ x .. (dlist_cons  _ _ z (dlist_nil ) ).. )) (at level  0): expr2_scope.
  Notation "'[' key '<-' v ']' " := ( Eset_regfile _ _ _  key v )(at level 0, no associativity) : expr2_scope.
  Notation "•" := (Enop _) : expr2_scope. 
  
  Definition mk_rule' {mem} env pat cond expr : rule mem :=
    mk_rule mem env env pat (where_clause_nil _ ) cond expr. 
