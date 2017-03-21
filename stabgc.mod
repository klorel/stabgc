# modularity bipartite : 
# (1/m) sum{r,b} (x[r,b]-d[r]*d[b]/m)
# pour C : (1/m) card(e in C) - (1/m)² d[R]*d[B]

param LB default 0; 
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

param PI_R{R} default 0;
param PI_B{B} default 0;


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


###
# stabilization
###
param N_BRANCHES := 2;
param WIDTH := 0.001;
param PENALTY default 2;
param CENTER_R{R} default 0;
param CENTER_B{B} default 0;

param FEAS_R{R} default 0;
param FEAS_B{B} default 0;
param FEAS_ERROR := max(max{r in R}abs(FEAS_R[r]), max{b in B}abs(FEAS_B[b]));

param OPT_ERROR default 0;

var z_R_pos{r in R, i in 1..N_BRANCHES} >= 0, <= PENALTY^i;
var z_R_neg{r in R, i in 1..N_BRANCHES} >= 0, <= PENALTY^i;

var z_B_pos{b in B, i in 1..N_BRANCHES} >= 0, <= PENALTY^i;
var z_B_neg{b in B, i in 1..N_BRANCHES} >= 0, <= PENALTY^i;

var x{ID} >= 0;

var modularity = +sum{id in ID}COLUMN_COST_USED[id]*x[id];

var c_dot_x = +sum{id in ID}COLUMN_COST_USED[id]*x[id];

maximize master_obj:
	+sum{id in ID}COLUMN_COST_USED[id]*x[id]
	
	+sum{r in R, i in 1..N_BRANCHES}z_R_neg[r, i]*(CENTER_R[r]-WIDTH*i)
	-sum{r in R, i in 1..N_BRANCHES}z_R_pos[r, i]*(CENTER_R[r]+WIDTH*i)
	
	+sum{b in B, i in 1..N_BRANCHES}z_B_neg[b, i]*(CENTER_B[b]-WIDTH*i)
	-sum{b in B, i in 1..N_BRANCHES}z_B_pos[b, i]*(CENTER_B[b]+WIDTH*i)
	;

subject to cover_r{r in R}: 
	+sum{id in ID}( if r in COLUMNS_R[id] then x[id] else 0)
	+sum{i in 1..N_BRANCHES}z_R_neg[r, i]
	-sum{i in 1..N_BRANCHES}z_R_pos[r, i]
	=
	1;
	
subject to cover_b{b in B}: 
	+sum{id in ID}( if b in COLUMNS_B[id] then x[id] else 0)
	+sum{i in 1..N_BRANCHES}z_B_neg[b, i]
	-sum{i in 1..N_BRANCHES}z_B_pos[b, i]
	=
	1;

param B_BAR := card(R)+card(B);

subject to fake_ctr:
	sum{id in ID} (card(COLUMNS_R[id])+card(COLUMNS_B[id])) * x[id] 
	<=
	B_BAR;
	

 
problem slave;

var yR{R} binary;
var yB{B} binary;

var w{R,B} >= 0;

subject to ctr_UU{r in R, b in B}: w[r,b] - yR[r] - yB[b] + 1 >=0;
subject to ctr_LU{r in R, b in B}: w[r,b] - yB[b] <=0;
subject to ctr_UL{r in R, b in B}: w[r,b] - yR[r] <=0;

var slave_modularity = +sum{r in R, b in B}(( if (r,b) in E then 1 else 0)-D_R[r]*D_B[b]*inv_m)*w[r,b]*inv_m;

var rc_pi = 
	+slave_modularity	
	-sum{r in R}PI_R[r]*yR[r]
	-sum{b in B}PI_B[b]*yB[b]
	;

var phi = 
	+slave_modularity	
	-sum{r in R}PI_R[r]*yR[r]
	-sum{b in B}PI_B[b]*yB[b]
	;

maximize reduced_cost:
	+sum{r in R, b in B}(( if (r,b) in E then 1 else 0)-D_R[r]*D_B[b]*inv_m)*w[r,b]*inv_m
	-sum{r in R}DUAL_FOR_R[r]*yR[r]
	-sum{b in B}DUAL_FOR_B[b]*yB[b]
	;