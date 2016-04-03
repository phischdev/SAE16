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
	all f: Function| f.*((firstStatement.*nextStatement).expression.calledFunction) != f
}

fact LastStatemenInList { 
	all f: Function | f.lastStatement in f.firstStatement.*nextStatement 
}


--------------------------Statement-----------------------------------------
---------------------------------------------------------------------------

abstract sig Statement {
	nextStatement: lone Statement,
	expression: lone Expr,
	owner: one Function 
}

sig AssignmentStatement  extends Statement{
	var: one Variable,
	expressions: one Expr
}

sig ReturnStatement extends Statement{}


fact StatementOwnership {
	all f: Function | all s: Statement | s in f.firstStatement.*nextStatement <=> s.owner = f
}


fact StatementHasOwner { all s: Statement | some f: Function | s.owner = f }


fact ReturnStatementHasExpression { all s: ReturnStatement | s.expression != none }
fact ReturnNoSucessor { all s: ReturnStatement | s.nextStatement = none }
fact StatementsHaveSuccessor { all s: Statement | s not in ReturnStatement =>s.nextStatement != none }
fact NotReflexive { all s: Statement | s.nextStatement != s }

fact StatementNoRecursion {
	all disj s1, s2: Statement | s1.nextStatement = s2 => s1 not in s2.^nextStatement
}

fact MaxOnePredecessor {
	all s: Statement | # {s1: Statement | s1.nextStatement = s} <= 1

}

fact MinOnePredecessor {
	all s: Statement | s not in Function.firstStatement => some s1: Statement | s1.nextStatement = s
}


fact FirstNoPredecessor { all s: Function.firstStatement | all s1: Statement | s1.nextStatement != s }

fact AssignmentTypeMatch{
	all a: AssignmentStatement |  p_subtypeOf [a.variable.type, a.expression.type]
}


fact FormalParameterCannotBeAssignedTo{
	all a: AssignmentStatement |all f: FormalParameter| (isTrue[a.var.declared]) && (a.var != f)
} 

fact OnlyNonDeclaredVariablesCanBeDeclared{
	all v: VarDecl | isFalse[v.variable.declared]
}


------------------------------Expression------------------------------------
---------------------------------------------------------------------------

sig Expr {
   type: one Type,
   children: set Expr,
   parent: lone Expr,
   owner: lone Statement,
   isParameter: one Bool
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
   all e: Expr | isFalse [e.isParameter] =>( e.owner = none <=> e.parent != none )
}

fact ExprAsParameterNoOwnerNorParent {
   all e: Expr | isTrue [e.isParameter] => e.owner = none && e.parent = none
}

fact IsParameterFact {
   all e: Expr | isTrue [e.isParameter] <=> some c: CallExpression | e in c.parameters
}

fact noExprRecursion{
   all e: Expr | (e not in e.^children) && (e != e.parent)
}

fact LiteralNoChildren {
   all e: Expr | all l: Literal | e.parent != l
}

fact ParentsMatchChildren {
 all e1, e2: Expr | e2 in e1.children <=> e2.parent = e1
}

fact ParamterTypeMatch {
    all e: CallExpression | all t: e.calledFunction.parameters.type |
        # { p: e.calledFunction.parameters | p.type = t } = # { p: e.parameters | p.type = t}
}

-------------------------Parameter-----------------------------------------
---------------------------------------------------------------------------

sig FormalParameter extends Variable{
	owner: one Function
}

fact FormalParameter{
	all f: Function | all p: FormalParameter | p in f.parameters <=> p.owner = f
}

fact FPHasOwner {
 all p: FormalParameter | some f: Function | p.owner = f
}

fact FormalParameterHasType{
	all f: FormalParameter | f.type != none
}

fact FormalParametersAreDeclaredAndAssigned{
	all f: FormalParameter | (isTrue[f.declared]) && (isTrue[f.assigned])
}

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


fact VarDeclNoExpr { all s: VarDecl | s.expression = none }


---------------------------------------------------------------------------
//----------------------Functions------------------------------------------
-------------------------------------------------------------------------

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
 f.firstStatement.*nextStatement
}

fun p_statementsAfter [s: Statement]: set Statement {
 s.^nextStatement
}

fun p_parameters [f: Function]: set FormalParameter {
 f.parameters
}

fun p_subexpr [e: Expr]: set Expr {
 e.children
}


---------------------------------------------------------------------------
------------------------------- Predicates —--------------------------------
---------------------------------------------------------------------------

pred p_containsCall [f: Function] {
 some x: CallExpression | x in f.*firstStatement.expression
}

pred p_isAssigned [v: Variable] {
 some f: Function | some s:AssignmentStatement | s in f.*firstStatement && v in s.var
}

pred p_isRead [v: Variable] {
	some r: VariableReference | v in r.reference
}


pred p_isDeclared [v: Variable] {
 	some f: Function | some s: VarDecl | s in f.*firstStatement && v in s.variable
}

pred p_isParameter[v:Variable]{
	some f: Function | v in f.parameters
} 

pred p_subtypeOf [t1: Type, t2: Type] {
 	t1 in t2.*parentType
}

pred p_assignsTo [s: Statement, vd: VarDecl] {
	vd.variable in s.var
}

pred hall{ 
	all u: Function | p_containsCall [u] 
	all v: Variable |p_isAssigned [v] 
	all v: Variable |p_isRead [v]
	all v: Variable| p_isDeclared [v] 

	all t1, t2: Type| p_subtypeOf [t1, t2]
	all s: Statement| all vd: VarDecl |p_assignsTo [s,vd] 
}


---------------------------------------------------------------------------
-------------------------------Show----------------------------------------
---------------------------------------------------------------------------
//pred show{}
//run show for 10


---------------------------------------------------------------------------
--------------------------------Task C-------------------------------------

/*
pred task1 {
	#Function = 1 
	#CallExpression = 2
}

run task1 for 4 

//Doesn't work


pred task2 {
	#Function = 2 
	#CallExpression = 2
}


run task2 for 4 */

//Doesn't work


pred task3 {
	#AssignmentStatement = 3
//	#Variable = 1
//	#Literal = 1
}


run task3 for 10

// Doesn't work

/*
pred task4{
	all a: AssignmentStatement | all c: CallExpression | 
	(c in a.expressions) && 
	(c.calledFunction.returnType != c.calledFunction.lastStatement.type ) &&
	(a.expressions.type != c.calledFunction.returnType)

}

run task4 for 7

*/
