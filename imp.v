(* FRANCESCO CECCONELLO VR457796 24/06/2023 *)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
From Coq Require Import Unicode.Utf8.

(* Definizione loc *)
Inductive loc : Type :=
  | Loc : nat -> loc.

(* Definizione del dizionario *)
Definition dizionario (A:Type) := loc -> A.

(* Definizione dello stato vuoto *)
Definition dizionario_vuoto {A:Type} (v : A) : dizionario A :=
  (fun _ => v).

(* Definizione dell'uguaglianza tra locazioni (serve per la funzione di aggiornamento) *)
Definition loc_eq loc1 loc2 :=
  match loc1, loc2 with
  | Loc n1, Loc n2 => n1 =? n2
  end.

(* Definizione dell'aggiornamento di un dizionario *)
Definition aggiorna_stato {A:Type} (m : dizionario A)
                    (x : loc) (v : A) :=
  fun x' => if loc_eq x x' then v else m x'.

(* Definizione degli stati *)
Definition stato := dizionario nat.

(* Stato vuoto *)
Definition stato_vuoto : stato :=
  dizionario_vuoto 0.

(* Definizione delle espressioni aritmetiche *)
Inductive aexp : Type :=
  | ANum : nat -> aexp
  | ALoc : loc -> aexp
  | APiu : aexp -> aexp -> aexp
  | AMeno : aexp -> aexp -> aexp
  | AMolt : aexp -> aexp -> aexp.

(* Definizione delle espressioni booleane *)
Inductive bexp : Type :=
  | BVero : bexp
  | BFalso : bexp
  | BNot : bexp -> bexp
  | BUguale : aexp -> aexp -> bexp
  | BMinoreUguale : aexp -> aexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  | BOr : bexp -> bexp -> bexp.

(* Definizione dei comandi *)
Inductive com : Type :=
  | CSkip : com
  | CAss : loc -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(* Funzione di valutazione per le espressioni aritmetiche *)
Fixpoint aeval (a : aexp) (st : stato) : nat :=
  match a with
  | ANum n => n
  | ALoc x => st x
  | APiu a1 a2 => (aeval a1 st) + (aeval a2 st)
  | AMeno a1 a2 => (aeval a1 st) - (aeval a2 st)
  | AMolt a1 a2 => (aeval a1 st) * (aeval a2 st)
  end.

(* Funzione di valutazione per le espressioni booleane *)
Fixpoint beval (b : bexp) (st : stato) : bool :=
  match b with
  | BVero => true
  | BFalso => false
  | BNot b' => negb (beval b' st)
  | BUguale a1 a2 => (aeval a1 st) =? (aeval a2 st)
  | BMinoreUguale a1 a2 => (aeval a1 st) <=? (aeval a2 st)
  | BAnd b1 b2 => andb (beval b1 st) (beval b2 st)
  | BOr b1 b2 => orb (beval b1 st) (beval b2 st)
  end.

Notation "a1 'mu' a2" := 
  (BMinoreUguale a1 a2) (at level 60, right associativity).
Notation "'Skip'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'While' b 'do' c " :=
  (CWhile b c) (at level 80, right associativity).
Notation "'If' c1 'then' c2 'else' c3" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(* Regole di valutazione per i comandi *)
Reserved Notation "'esegui' c1 'in' st 'ritorna' st'" (at level 40, st at level 39).

Inductive ceval : com -> stato -> stato -> Prop :=
| eval_CSkip : forall st,
    esegui CSkip in st ritorna st
| eval_CAss : forall st a1 n x,
    aeval a1 st = n ->
    esegui (x ::= a1) in st ritorna (aggiorna_stato st x n)
| eval_CSeq : forall c1 c2 st st' st'',
    esegui c1 in st ritorna st' ->
    esegui c2 in st' ritorna st'' ->
    esegui (c1 ;; c2) in st ritorna st''
| eval_CIfTrue : forall st st' b c1 c2,
    beval b st = true ->
    esegui c1 in st ritorna st' ->
    esegui (CIf b c1 c2) in st ritorna st'
| eval_CIfFalse : forall st st' b c1 c2,
    beval b st = false ->
    esegui c2 in st ritorna st' ->
    esegui (CIf b c1 c2) in st ritorna st'
| eval_CWhileFalse : forall b st c,
    beval b st = false ->
    esegui (CWhile b c) in st ritorna st
| eval_CWhileTrue : forall st st' st'' b c,
    beval b st = true ->
    esegui c in st ritorna st' ->
    esegui (CWhile b c) in st' ritorna st'' ->
    esegui (CWhile b c) in st ritorna st''

where "'esegui' c1 'in' st 'ritorna' st'" := (ceval c1 st st').

(* Definizione relazione di equivalenza fra comandi come da slloce *)
Definition cequiv (c1 c2 : com) : Prop :=
  ∀(st st' : stato),
    (esegui c1 in st ritorna st') ↔ (esegui c2 in st ritorna st').

Theorem equivalenza_if_while: ∀ (b: bexp) (c: com),
  cequiv
    (While b do c)
    (If b then (c;; While b do c) else Skip).
Proof.
  intros b c st st'. (* introduzione delle ipotesi *)
  split. (* split della doppia implicazione *)
  intros Hce. (* introduzione della condizione di equivalenza *)
  - (* -> *)
    inversion Hce; subst. (* in questo caso st = st', cioè non sono entrato nel ciclo *)
    + (* non entro nel ciclo*)
      apply eval_CIfFalse. (* quindi la guardia è falsa *)
      assumption. (* il subgoal è già presente nelle ipotesi *)
      apply eval_CSkip. (* valuto il comando Skip, posso farlo perché st' = st' *)
    + (* entro nel ciclo *)
      apply eval_CIfTrue. (* la guardia ora è vera per ipotesi H1 *)
      assumption. (* il subgoal è già presente nelle ipotesi *)
      apply eval_CSeq with (st' := st'0). (* applico la valutazione di Seq *)
      assumption. (* il subgoal è già presente nelle ipotesi *)
      assumption. (* il subgoal è già presente nelle ipotesi *)
  - (* <- *)
    intros Hce. (* introduzione della condizione di equivalenza *)
    inversion Hce; subst. (* in questo caso b = true, cioè sono entrato nel ciclo *)
    + (* entro nel ciclo *)
      inversion H5. subst. (* introduco lo stato vuoto *)
      apply eval_CWhileTrue with (st' := st'0). (* applico la valutazione del branch true del while *)
      assumption. (* il subgoal è già presente nelle ipotesi *)
      assumption. (* il subgoal è già presente nelle ipotesi *)
      assumption. (* il subgoal è già presente nelle ipotesi *)
    + (* non entro nel ciclo *)
      inversion H5. (* la guardia ora è vera per ipotesi H4 *)
      subst. 
      apply eval_CWhileFalse.  (* applico la valutazione del branch false del while *)
      assumption. (* il subgoal è già presente nelle ipotesi *)
Qed.

(* Definisco le variabili X e Y dell'algoritmo *)
Definition X : loc := Loc 0.
Definition Y : loc := Loc 1.

(* Definisco lo stato finale descrivendo l'andamento dello stato durante l'esecuzione del programma *)
Definition stato_finale : stato := 
    (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1) Y 6) X 0) Y 12).

Example algoritmo:
  esegui
  (X ::= ANum 2;; (* x = 2 *)
   Y ::= ANum 3;; (* y = 3 *)
   While BMinoreUguale (ANum 1) (ALoc X) do (* controllo della condizione *)
     X ::= AMeno (ALoc X) (ANum 1);; (* x = x -1 *)
     Y ::= AMolt (ANum 2) (ALoc Y)   (* y = y * 2 *)
   )
  in 
    stato_vuoto
  ritorna 
    stato_finale. (* sequenza di cambiamento degli stati *)
Proof.
  apply eval_CSeq with (aggiorna_stato stato_vuoto X 2). (* aggiungo X = 2 allo stato vuoto *)
  - apply eval_CAss. reflexivity. (* applico l'assegnamento *)
  - apply eval_CSeq with (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3). (* aggiungo X = 2, Y = 3 allo stato vuoto *)
    + apply eval_CAss. reflexivity. (* applico l'assegnamento *)
    + apply eval_CWhileTrue with 
            (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1) Y 6). (* la condizione è vera *)
      * reflexivity. (* entro nel ciclo riportando lo stato finale dopo la prima iterazione con X = 1 e Y = 6*)
      * apply eval_CSeq with (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1). (* aggiorno lo stato *)
        ** apply eval_CAss. reflexivity. (* assegno X *)
        ** apply eval_CAss. reflexivity. (* assegno Y *)
      * apply eval_CWhileTrue with 
            (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1) Y 6) X 0) Y 12).
            (* la condizione è ancora vera, quindi devo rientrare nel ciclo con lo stato precedente e riportando lo stato finale dopo la seconda iterazione *)
            (* con X = 0 e Y = 12 *)
        ** reflexivity. (* entro nel ciclo *)
        ** apply eval_CSeq with (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato (aggiorna_stato stato_vuoto X 2) Y 3) X 1) Y 6) X 0). (* aggiorno lo stato *)
           *** apply eval_CAss. reflexivity. (* assegno X *)
           *** apply eval_CAss. reflexivity. (* assegno Y *)
        ** apply eval_CWhileFalse. reflexivity. (* la condizione è falsa, quindi esco dal ciclo *)
Qed.
