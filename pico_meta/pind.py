from __future__ import print_function
import sys
from pacolib import *
if len(sys.argv) < 2:
    sys.stderr.write("\nUsage: "+sys.argv[0]+" relsize\n\n")
    sys.exit(1)
n = int(sys.argv[1])

print ("Require Export Program.Basics. Open Scope program_scope.")
print ("From Paco Require Import paco.")
print ("From Paco Require Import paconotation_internal paco_internal pacotac_internal.")
print ("From Paco Require Export paconotation.")
print ("From Fairness Require Import pind_internal.")
print ("Set Implicit Arguments.")
print ("")
print ("Section PIND"+str(n)+".")
print ("")
for i in range(n):
    print ("Variable T"+str(i)+" : "+ifpstr(i,"forall"),end="")
    for j in range(i):
        print (" (x"+str(j)+": @T"+str(j)+itrstr(" x",j)+")",end="")
    print (ifpstr(i,", ")+"Type.")
print ("")
print ("(** ** Predicates of Arity "+str(n)+"")
print ("*)")
print ("")
print ("Definition pind"+str(n)+"(gf : rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")(r: rel"+str(n)+""+itrstr(" T", n)+") : rel"+str(n)+""+itrstr(" T", n)+" :=")
print ("  @curry"+str(n)+itrstr(" T", n)+" (pind (fun R0 => @uncurry"+str(n)+itrstr(" T", n)+" (gf (@curry"+str(n)+itrstr(" T", n)+" R0))) (@uncurry"+str(n)+itrstr(" T", n)+" r)).")
print ("")
print ("Definition upind"+str(n)+"(gf : rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")(r: rel"+str(n)+""+itrstr(" T", n)+") := pind"+str(n)+" gf r /"+str(n)+"\\ r.")
print ("Arguments pind"+str(n)+" : clear implicits.")
print ("Arguments upind"+str(n)+" : clear implicits.")
print ("#[local] Hint Unfold upind"+str(n)+" : core.")
print ("")
print ("Lemma monotone"+str(n)+"_inter (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+")")
print ("      (MON1: monotone"+str(n)+" gf)")
print ("      (MON2: monotone"+str(n)+" gf'):")
print ("  monotone"+str(n)+" (gf /"+str(n+1)+"\\ gf').")
print ("Proof.")
print ("  red; intros. destruct IN. split; eauto.")
print ("Qed.")
print ("")
print ("Lemma _pind"+str(n)+"_mon_gen (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r r'")
print ("    (LEgf: gf <"+str(n+1)+"= gf')")
print ("    (LEr: r <"+str(n)+"= r'):")
print ("  pind"+str(n)+" gf r <"+str(n)+"== pind"+str(n)+" gf' r'.")
print ("Proof.")
print ("  apply curry_map"+str(n)+". red; intros. eapply pind_mon_gen. apply PR.")
print ("  - intros. apply LEgf, PR0.")
print ("  - intros. apply LEr, PR0.")
print ("Qed.")
print ("")
print ("Lemma pind"+str(n)+"_mon_gen (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r r'"+itrstr(" x", n)+"")
print ("    (REL: pind"+str(n)+" gf r"+itrstr(" x", n)+")")
print ("    (LEgf: gf <"+str(n+1)+"= gf')")
print ("    (LEr: r <"+str(n)+"= r'):")
print ("  pind"+str(n)+" gf' r'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply _pind"+str(n)+"_mon_gen; [apply LEgf | apply LEr | apply REL].")
print ("Qed.")
print ("")
print ("Lemma pind"+str(n)+"_mon_bot (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r'"+itrstr(" x", n)+"")
print ("    (REL: pind"+str(n)+" gf bot"+str(n)+""+itrstr(" x", n)+")")
print ("    (LEgf: gf <"+str(n+1)+"= gf'):")
print ("  pind"+str(n)+" gf' r'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply pind"+str(n)+"_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].")
print ("Qed.")
print ("")

print ("Definition top"+str(n)+ifpstr(n," {")+itrstr(" T",n)+ifpstr(n,"}"),end="")
for i in range(n):
    print (" (x"+str(i)+": T"+str(i)+itrstr(" x",i)+")",end='')
print (" := True.")
print ("")
print ("Lemma pind"+str(n)+"_mon_top (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r"+itrstr(" x", n)+"")
print ("    (REL: pind"+str(n)+" gf r"+""+itrstr(" x", n)+")")
print ("    (LEgf: gf <"+str(n+1)+"= gf'):")
print ("  pind"+str(n)+" gf' top"+str(n)+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply pind"+str(n)+"_mon_gen; eauto. red. auto.")
print ("Qed.")
print ("")

print ("Lemma upind"+str(n)+"_mon_gen (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r r'"+itrstr(" x", n)+"")
print ("    (REL: upind"+str(n)+" gf r"+itrstr(" x", n)+")")
print ("    (LEgf: gf <"+str(n+1)+"= gf')")
print ("    (LEr: r <"+str(n)+"= r'):")
print ("  upind"+str(n)+" gf' r'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  destruct REL. split; eauto.")
print ("  eapply pind"+str(n)+"_mon_gen; [apply H | apply LEgf | apply LEr].")
print ("Qed.")
print ("")
print ("Lemma upind"+str(n)+"_mon_bot (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r'"+itrstr(" x", n)+"")
print ("    (REL: upind"+str(n)+" gf bot"+str(n)+""+itrstr(" x", n)+")")
print ("    (LEgf: gf <"+str(n+1)+"= gf'):")
print ("  upind"+str(n)+" gf' r'"+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply upind"+str(n)+"_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].")
print ("Qed.")
print ("")

print ("Lemma upind"+str(n)+"mon_top (gf gf': rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+") r"+itrstr(" x", n)+"")
print ("    (REL: upind"+str(n)+" gf r"+""+itrstr(" x", n)+")")
print ("    (LEgf: gf <"+str(n+1)+"= gf'):")
print ("  upind"+str(n)+" gf' top"+str(n)+itrstr(" x", n)+".")
print ("Proof.")
print ("  eapply upind"+str(n)+"_mon_gen; eauto. red. auto.")
print ("Qed.")
print ("")

print ("Section Arg"+str(n)+".")
print ("")
print ("Variable gf : rel"+str(n)+""+itrstr(" T", n)+" -> rel"+str(n)+""+itrstr(" T", n)+".")
print ("Arguments gf : clear implicits.")
print ("")
print ("Theorem _pind"+str(n)+"_mon: _monotone"+str(n)+" (pind"+str(n)+" gf).")
print ("Proof.")
print ("  red; intros. eapply curry_map"+str(n)+", _pind_mon; apply uncurry_map"+str(n)+"; assumption.")
print ("Qed.")
print ("")
print ("Theorem _pind"+str(n)+"_acc: forall")
print ("  l r (OBG: forall rr (DEC: rr <"+str(n)+"== r) (IH: rr <"+str(n)+"== l), pind"+str(n)+" gf rr <"+str(n)+"== l),")
print ("  pind"+str(n)+" gf r <"+str(n)+"== l.")
print ("Proof.")
print ("  intros. apply curry_adjoint2_"+str(n)+".")
print ("  eapply _pind_acc. intros.")
print ("  apply curry_adjoint2_"+str(n)+" in DEC. apply curry_adjoint2_"+str(n)+" in IH.")
print ("  apply curry_adjoint1_"+str(n)+".")
print ("  eapply le"+str(n)+"_trans. 2: eapply (OBG _ DEC IH).")
print ("  apply curry_map"+str(n)+".")
print ("  apply _pind_mon; try apply le1_refl; apply curry_bij2_"+str(n)+".")
print ("Qed.")
print ("")
print ("Theorem _pind"+str(n)+"_mult_strong: forall r,")
print ("  pind"+str(n)+" gf r <"+str(n)+"== pind"+str(n)+" gf (upind"+str(n)+" gf r).")
print ("Proof.")
print ("  intros. apply curry_map"+str(n)+".")
print ("  eapply le1_trans; [eapply _pind_mult_strong |].")
print ("  apply _pind_mon; intros [] H. apply H.")
print ("Qed.")
print ("")
print ("Theorem _pind"+str(n)+"_fold: forall r,")
print ("  gf (upind"+str(n)+" gf r) <"+str(n)+"== pind"+str(n)+" gf r.")
print ("Proof.")
print ("  intros. apply uncurry_adjoint1_"+str(n)+".")
print ("  eapply le1_trans; [| apply _pind_fold]. apply le1_refl.")
print ("Qed.")
print ("")
print ("Theorem _pind"+str(n)+"_unfold: forall (MON: _monotone"+str(n)+" gf) r,")
print ("  pind"+str(n)+" gf r <"+str(n)+"== gf (upind"+str(n)+" gf r).")
print ("Proof.")
print ("  intros. apply curry_adjoint2_"+str(n)+".")
print ("  eapply _pind_unfold; apply monotone"+str(n)+"_map; assumption.")
print ("Qed.")
print ("")
print ("Theorem pind"+str(n)+"_acc: forall")
print ("  l r (OBG: forall rr (DEC: rr <"+str(n)+"= r) (IH: rr <"+str(n)+"= l), pind"+str(n)+" gf rr <"+str(n)+"= l),")
print ("  pind"+str(n)+" gf r <"+str(n)+"= l.")
print ("Proof.")
print ("  apply _pind"+str(n)+"_acc.")
print ("Qed.")
print ("")
print ("Theorem pind"+str(n)+"_mon: monotone"+str(n)+" (pind"+str(n)+" gf).")
print ("Proof.")
print ("  apply monotone"+str(n)+"_eq.")
print ("  apply _pind"+str(n)+"_mon.")
print ("Qed.")
print ("")
print ("Theorem upind"+str(n)+"_mon: monotone"+str(n)+" (upind"+str(n)+" gf).")
print ("Proof.")
print ("  red; intros.")
print ("  destruct IN. split; eauto.")
print ("  eapply pind"+str(n)+"_mon. apply H. apply LE.")
print ("Qed.")
print ("")
print ("Theorem pind"+str(n)+"_mult_strong: forall r,")
print ("  pind"+str(n)+" gf r <"+str(n)+"= pind"+str(n)+" gf (upind"+str(n)+" gf r).")
print ("Proof.")
print ("  apply _pind"+str(n)+"_mult_strong.")
print ("Qed.")
print ("")
print ("Corollary pind"+str(n)+"_mult: forall r,")
print ("  pind"+str(n)+" gf r <"+str(n)+"= pind"+str(n)+" gf (pind"+str(n)+" gf r).")
print ("Proof. intros; eapply pind"+str(n)+"_mult_strong in PR. eapply pind"+str(n)+"_mon; eauto. intros. destruct PR0. eauto. Qed.")
print ("")
print ("Theorem pind"+str(n)+"_fold: forall r,")
print ("  gf (upind"+str(n)+" gf r) <"+str(n)+"= pind"+str(n)+" gf r.")
print ("Proof.")
print ("  apply _pind"+str(n)+"_fold.")
print ("Qed.")
print ("")
print ("Theorem pind"+str(n)+"_unfold: forall (MON: monotone"+str(n)+" gf) r,")
print ("  pind"+str(n)+" gf r <"+str(n)+"= gf (upind"+str(n)+" gf r).")
print ("Proof.")
print ("  intro. eapply _pind"+str(n)+"_unfold; apply monotone"+str(n)+"_eq; assumption.")
print ("Qed.")
print ("")
print ("End Arg"+str(n)+".")
print ("")
print ("Arguments pind"+str(n)+"_acc : clear implicits.")
print ("Arguments pind"+str(n)+"_mon : clear implicits.")
print ("Arguments upind"+str(n)+"_mon : clear implicits.")
print ("Arguments pind"+str(n)+"_mult_strong : clear implicits.")
print ("Arguments pind"+str(n)+"_mult : clear implicits.")
print ("Arguments pind"+str(n)+"_fold : clear implicits.")
print ("Arguments pind"+str(n)+"_unfold : clear implicits.")
print ("")
print ("End PIND"+str(n)+".")
print ("")
print ("Global Opaque pind"+str(n)+".")
print ("")
print ("#[export] Hint Unfold upind"+str(n)+" : core.")
print ("#[export] Hint Resolve pind"+str(n)+"_fold : core.")
print ("#[export] Hint Unfold monotone"+str(n)+" : core.")
print ("")