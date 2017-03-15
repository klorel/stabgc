# modularity bipartite : 
# (1/m) sum{r,b} (x[r,b]-d[r]*d[b]/m)
# pour C : (1/m) card(e in C) - (1/m)² d[R]*d[B]
 
set E dimen 2;

param m := card(E);
param inv_m := 1/m;

set R := union{(r,b) in E}{r};
set B := union{(r,b) in E}{b};

param MAX_R := max{r in R}r;

set V := R union setof{b in B}(MAX_R+b);

param D_R{r in R} := card({(r,b) in E});
param D_B{b in B} := card({(r,b) in E});

set ID default {};
param CURRENT_ID default 0;

set COLUMNS_R{ID} default {};
set COLUMNS_B{ID} default {};

param COLUMN_E{id in ID} := card((COLUMNS_R[id] cross COLUMNS_B[id]) inter E);

param COLUMN_DR{id in ID} := sum{r in COLUMNS_R[id]}D_R[r];
param COLUMN_DB{id in ID} := sum{b in COLUMNS_B[id]}D_B[b];
 
param COLUMN_COST{id in ID} := 
	+inv_m*COLUMN_E[id]
	-inv_m*inv_m*COLUMN_DR[id]*COLUMN_DB[id];
	
param COLUMN_COST_USED{id in ID} := if abs(COLUMN_COST[id])>1e-6 then COLUMN_COST[id] else 0;


param DUAL_FOR_R{R} default 0;
param DUAL_FOR_B{B} default 0;


set TMP_R default {};
set TMP_B default {};

param TMP_E := card((TMP_R cross TMP_B) inter E);

param TMP_DR := sum{r in TMP_R}D_R[r];
param TMP_DB := sum{b in TMP_B}D_B[b];
 
param TMP_COST := 
	+inv_m*TMP_E
	-inv_m*inv_m*TMP_DR*TMP_DB;
	
param TMP_REDUCED_COST:= 
	+TMP_COST
	-sum{r in R}DUAL_FOR_R[r]
	-sum{b in B}DUAL_FOR_B[b]
	;

problem master;

var x{ID} >= 0;

maximize modularity: sum{id in ID}COLUMN_COST_USED[id]*x[id];

subject to cover_r{r in R}: 
	sum{id in ID} if r in COLUMNS_R[id] then x[id] else 0
	=
	1;
	
subject to cover_b{b in B}: 
	sum{id in ID} if b in COLUMNS_B[id] then x[id] else 0
	=
	1;

subject to fake_ctr:
	sum{id in ID} (card(COLUMNS_R[id])+card(COLUMNS_B[id])) * x[id] 
	=
	card(R)+card(B);
 
problem slave;

var yR{R} binary;
var yB{B} binary;

var w{R,B} >= 0;

subject to ctr_UU{r in R, b in B}: w[r,b] - yR[r] - yB[b] + 1 >=0;
subject to ctr_LU{r in R, b in B}: w[r,b] - yB[b] <=0;
subject to ctr_UL{r in R, b in B}: w[r,b] - yR[r] <=0;

maximize reduced_cost:
	+sum{r in R, b in B}(( if (r,b) in E then 1 else 0)-D_R[r]*D_B[b]*inv_m)*w[r,b]*inv_m
	-sum{r in R}DUAL_FOR_R[r]*yR[r]
	-sum{b in B}DUAL_FOR_B[b]*yB[b]
	;
	