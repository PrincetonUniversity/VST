
Require Import compcert.common.Memory.
From veric Require Import shares juicy_mem.
Require Import msl.msl_standard.


  Lemma perm_of_glb_not_Freeable: forall sh,
      ~ perm_of_sh (Share.glb Share.Rsh sh) = Some Freeable.
    (*Andrew says this is easy*)
  Admitted.
  Lemma writable_not_join_readable:
    forall sh1 sh2,
      joins sh1 sh2 ->
      writable_share sh1 ->
      ~ readable_share sh2.
    (*Andrew can probably proof this*)
  Admitted. 
  Lemma writable_not_join_writable :
    forall sh1 sh2,
      joins sh1 sh2 ->
      writable_share sh1 ->
      ~ writable_share sh2.
    (*Andrew can probably proof this*)
  Admitted. 
  Lemma only_bot_joins_top:
    forall sh, joins Share.top sh -> sh = Share.bot.
    (*Andrew can probably proof this*)
  Admitted.
  Lemma glb_Rsh_not_top:
    forall sh, ~ Share.glb Share.Rsh sh = Share.top.
    (*Andrew can probably proof this*)
  Admitted.
  Lemma writable_right:
    forall sh,  writable_share (Share.glb Share.Rsh sh) ->
           writable_share sh.
    (*Andrew can probably proof this*)
  Admitted.

Lemma join_readable_unreadable:
  forall sh1 sh2 sh3,
    join sh1 sh2 sh3 ->
    ~ shares.writable_share sh1 ->
    ~ shares.readable_share sh2 ->
    ~ shares.writable_share sh3.
Admitted.

Lemma readable_glb:
   forall sh,
     shares.readable_share sh ->
     shares.readable_share (Share.glb Share.Rsh sh).
 Admitted.
 Lemma unreadable_glb:
   forall sh,
     ~shares.readable_share sh ->
     ~shares.readable_share (Share.glb Share.Rsh sh).
 Admitted.

 