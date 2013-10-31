app load ["realTheory","TargetRewrite"];

open realTheory ImpRewrite TargetRewrite;

g `!x. x < 0 ==> (x / x * y = y)`;

e (IMP_REWRITE_TAC[REAL_DIV_REFL,REAL_MUL_LID]);

g `x+y+(-x)=(y:real)`;

e(TARGET_REWRITE_TAC[REAL_ADD_ASSOC,REAL_ADD_SYM] REAL_ADD_RINV);

g `!x y. inv y * x * y = x`;

e(TARGET_REWRITE_TAC[REAL_MUL_ASSOC,REAL_MUL_SYM] REAL_MUL_RINV);

app load ["complexTheory"];

open complexTheory;

g `!z. modu (conj z) = modu z`;

e (TARGET_REWRITE_TAC[GSYM EULER_FORMULE] CONJ_SCALAR_LMUL);

g `!P Q R S. P 1 /\ Q 2 /\ R 3 ==> ?x y. P x /\ R y /\ S x y`;

e HINT_EXISTS_TAC;
