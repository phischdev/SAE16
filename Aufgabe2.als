//------------------Project 1------------------------------------------------
//-------------------------------------------------------------------------
//------------Philipp Schimmelfennig -Panuya Balasuntharam----------------------
//-------------------------------------------------------------------------


// Boolean
abstract sig Bool {}
one sig True, False extends Bool {}

pred isTrue[b: Bool] { b in True }

pred isFalse[b: Bool] { b in False }

fun Not[b: Bool] : Bool {
 Bool - b
}

fun And[b1, b2: Bool] : Bool {
 subset_[b1 + b2, True]
}

fun Or[b1, b2: Bool] : Bool {
 subset_[True, b1 + b2]
}

fun Xor[b1, b2: Bool] : Bool {
 subset_[Bool, b1 + b2]
}

fun Nand[b1, b2: Bool] : Bool {
 subset_[False, b1 + b2]
}

fun Nor[b1, b2: Bool] : Bool {
 subset_[b1 + b2, False]
}

fun subset_[s1, s2: set Bool] : Bool {
 (s1 in s2) => True else False
}

--------------------------------------------------------------------------


sig LinearProgram{
	functions: some Function,
	mainFunction: one Function
}


fact {
	#LinearProgram = 1 
}

--------------------------Type---------------------------------------------
---------------------------------------------------------------------------

sig Type {
	parentType: lone Type
}

fact notOwnParent { 
	all t: Type | t.parentType != t 
}

fact noRecursion { 
	all disj t1, t2: Type | p_subtypeOf[t1, t2] => not p_subtypeOf[t2, t1] 
}

----------------------------Function----------------------------------------
---------------------------------------------------------------------------


sig Function {
	returnType: one Type, 
	parameters: set FormalParameter,
	owner: one LinearProgram, 
	firstStatement: one Statement,
	lastStatement: one ReturnStatement,
}

fact belongsToFunction{
	all f: Function | all l:LinearProgram | l in f.owner <=> f in l.functions
}

fact functionsHasOwner {
	all f: Function | some l: LinearProgram | f in l.functions
} 

fact mainFunctionHasNoParameter{
	all m: LinearProgram.mainFunction | m.parameters= none
}

fact mainFunctionBelongsToAFunction{
	all m: LinearProgram.mainFunction | all p: LinearProgram | p.mainFunction = m => m in p.functions
}

fact mainFunctionCannotBeCalled {
	all f: LinearProgram.mainFunction | all e: CallExpression | e.calledFunction != f
}

fact avoidRecursion{
	--all f: Function| f.*(sequence.statements.expression.calledFunction) != f
}

fact LastStatemenInList { all f: Function | f.lastStatement in f.firstStatement.*nextStatement }


--------------------------Statement-----------------------------------------
---------------------------------------------------------------------------

abstract sig Statement {
	nextStatement: lone Statement,
	expression: lone Expr,
	owner: one Function 
}

sig AssignmentStatement  extends Statement{
	//var: one Variable,
	expressions: one Expr
}

sig ReturnStatement extends Statement{}


fact StatementOwnership {
	all f: Function | all s: Statement | s in f.firstStatement.*nextStatement <=> s.owner = f
}
<<<<<<< HEAD

fact StatementHasOwner { all s: Statement | some f: Function | s.owner = f }

=======

fact StatementHasOwner { all s: Statement | some f: Function | s.owner = f }

>>>>>>> origin/master
fact ReturnStatementHasExpression { all s: ReturnStatement | s.expression != none }
fact ReturnNoSucessor { all s: ReturnStatement | s.nextStatement = none }
fact StatementsHaveSuccessor { all s: Statement | s not in ReturnStatement =>s.nextStatement != none }
fact NotReflexive { all s: Statement | s.nextStatement != s }

fact StatementNoRecursion {
	all disj s1, s2: Statement | s1.nextStatement = s2 => s1 not in s2.^nextStatement
}

fact MaxOnePredecessor {
	all s: Statement | # {s1: Statement | s1.nextStatement = s} <= 1
<<<<<<< HEAD
}

fact MinOnePredecessor {
	all s: Statement | s not in Function.firstStatement => some s1: Statement | s1.nextStatement = s
}

=======
}

fact MinOnePredecessor {
	all s: Statement | s not in Function.firstStatement => some s1: Statement | s1.nextStatement = s
}

>>>>>>> origin/master
fact FirstNoPredecessor { all s: Function.firstStatement | all s1: Statement | s1.nextStatement != s }

fact{
--	all a: AssignmentStatement |  p_subtypeOf [a.variable.type, a.expression.type]
}



------------------------------Expression------------------------------------
---------------------------------------------------------------------------

sig Expr {
	type: one Type,
	children: set Expr,
	parent: lone Expr,
	owner: lone Statement
}

sig Literal extends Expr {}

sig CallExpression extends Expr {
	calledFunction: one Function,
	parameters: set Expr
}

fact ExpressionOwnership {
	all e: Expr | all s: Statement | e.owner = s <=> s.expression = e
}

fact HasParentOrOwner {
	all e: Expr | e.owner = none <=> e.parent != none
}

fact noExprRecursion{
	all e: Expr | (e not in e.^children) && (e != e.parent)
}

fact LiteralNoChildren {
	all e: Expr | all l: Literal | e.parent != l
}

/*
fact MatchesParameters {
 	all e: CallExpression | # e.calledFunction.parameters = # e.parameters
}*/

-------------------------Parameter-----------------------------------------
---------------------------------------------------------------------------

sig FormalParameter extends Variable{
	owner: one Function
}

fact FormalParameter{
<<<<<<< HEAD
	all f: Function | all p: FormalParameter | p in f.parameters <=> p.owner = f
=======
	all f: Function | all p: FormalParameter | p in f.formalParameters <=> p.owner = f
>>>>>>> origin/master
}

fact FPHasOwner {
 all p: FormalParameter | some f: Function | p.owner = f
}

fact {
	all f: FormalParameter | f.type != none
}

fact{
	all f: FormalParameter | (f.declared= True) && (f.assigned = True)
}
---------------------------Expression Tree-----------------------
/*sig Node {
	parent: lone Node,
	children: set Node,
	exprTree: one ExpressionTree
}

sig ExpressionTree {
	root: one Node,
	leaves: set Node
}


fact parentChildrenRelationsship{
	all n1, n2: Node | n1. parent = n2  <=> n1 in n2.children 
}


// unsicher ob dies funktioniert. Ich möchte root definieren
fact root{
	(all r: ExpressionTree | all n: Node | r.root in n.^parent)&&
	(all r: ExpressionTree | all n: Node | r. root not in n.^children)
}

fact notSameRootAndLeaves{
	all e: ExpressionTree | e.root not in e.leaves
}

fact notOwnChild {
	all n: Node | n not in n.children
}

fact notOwnParent{
	all n: Node | n not in n.parent
}

fact notSameRoot{
	all e1, e2: ExpressionTree | e1.root != e2.root
}

fact parentAndChildHasTheSameExprTree {
	all n1, n2: Node | n1.parent = n2 => n1.exprTree = n2.exprTree
}


*/
-------------------------------Variable-------------------------------------
---------------------------------------------------------------------------


sig Variable {
	declared: one Bool, 
	assigned: one Bool, 
	type: lone Type
}

sig VariableReference extends Expr{
	reference: one Variable
}

sig VarDecl extends Statement{
	type: one Type,
	variable: one Variable
} 

fact{
#AssignmentStatement >2
}


// Variable and its VariableReference should have the same type
fact{
	all v: Variable|all r: VariableReference | (r.reference = v => r.type = v.type)
}



fact {
	all v: Variable|all r: VariableReference | (v.type = none) => (v not in r.reference)
}

fact {
	all c: CallExpression | c not in c.parameters
}

fact {
	all a: AssignmentStatement |all f: FormalParameter| (a.var.declared = True) && (a.var != f)
} 

fact {
	all v: VarDecl | v.variable.declared = False
}

/*
---------------------------------------------------------------------------
//----------------------Functions--------------------------------------------
---------------------------------------------------------------------------

fun p_numFunctionCalls[]: Int {
 # CallExpression
}

fun p_expressionTypes[]:set Type {
 Expr.type
}

fun p_literalTypes[]:set Type {
 Literal.type
}

fun p_statementsInFunction [f: Function]: set Statement {
 f.sequence.statements
}

fun p_statementsAfter [s: Statement]: set Statement {
 s.*nextStatement
}

fun p_parameters [f: Function]: set FormalParameter {
 f.formalParameters
}



fun p_subexpr [e: Expr]: set Expr {
 e.children
}

*/
---------------------------------------------------------------------------
------------------------------- Predicates —--------------------------------
---------------------------------------------------------------------------
/*
pred p_containsCall [f: Function] {
 some x: CallExpression | x in f.sequence.statements.expression
}

--TODO: Problem: Main Function is called by functions

pred p_isAssigned [v: Variable] {
 some f: Function | some s:AssignmentStatement | s in f.sequence.statements && v in s.var
}



pred p_isRead [v: Variable] {
 #(v.readIn) != 0 
}


pred p_isDeclared [v: Variable] {
 	some f: Function | some s: VarDecl | s in f.sequence.statements && v in s.variable
}

//TODO: doesn't work


pred p_isParameter[v:Variable]{} // TODO
*/
pred p_subtypeOf [t1: Type, t2: Type] {
 	t1 in t2.*parentType
}
/*
pred p_assignsTo [s: Statement, vd: VarDecl] {
	vd.variable in s.var
}
*/
pred hall{ 
--	all u: Function | p_containsCall [u] 
--	all v: Variable |p_isAssigned [v] 
--	all v: Variable |p_isRead [v]
--	all v: Variable| p_isDeclared [v] 

--all t1, t2: Type| p_subtypeOf [t1, t2]
--	all s: Statement| all vd: VarDecl |p_assignsTo [s,vd] 
}


pred show{}

run show for 5
