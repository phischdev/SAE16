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
	all f: Function|not f in f.^((firstStatement.*nextStatement).expression.calledFunction)
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
	var: one Variable
}

sig ReturnStatement extends Statement{}


fact StatementOwnership {
	all f: Function | all s: Statement | s in f.firstStatement.*nextStatement <=> s.owner = f
}


fact StatementHasOwner { 
	all s: Statement | some f: Function | s.owner = f 
}

fact ReturnStatementTypeMatchFunctionType{
	all s: ReturnStatement | p_subtypeOf [s.owner.returnType, s.expression.type]
}

fact ReturnStatementHasExpression { 
	all s: ReturnStatement | s.expression != none 
}

fact AssignmentStatementHasExpression {
	all s: AssignmentStatement | s.expression != none 
}

fact ReturnNoSucessor { 
	all s: ReturnStatement | s.nextStatement = none 
}

fact StatementsHaveSuccessor { 
	all s: Statement | not s in ReturnStatement =>s.nextStatement != none 
}

fact NotReflexive { 
	all s: Statement | s.nextStatement != s 
}

fact StatementNoRecursion {
	all disj s1, s2: Statement | s1.nextStatement = s2 =>not s1 in s2.^nextStatement
}

fact MaxOnePredecessor {
	all s: Statement | # {s1: Statement | s1.nextStatement = s} <= 1

}

fact MinOnePredecessor {
	all s: Statement | not s  in Function.firstStatement => some s1: Statement | s1.nextStatement = s
}


fact FirstNoPredecessor { 
	all s: Function.firstStatement | all s1: Statement | s1.nextStatement != s 
}

fact AssignmentTypeMatch{
	all a: AssignmentStatement |  p_subtypeOf [  a.var.type, a.expression.type]
}

fact FormalParameterCannotBeAssignedTo{
--	all a: AssignmentStatement |not a.var in FormalParameter
} 

fact DeclarationBeforeAssignment {
	all s: AssignmentStatement | some d: VarDecl | s.var = d.variable => s in d.^nextStatement
}

fact DeclarationBeforeRead{
	all v: VariableReference | some d: VarDecl | not v.reference in FormalParameter && v.reference = d.variable => ExpOwnerSt[v] in d.^nextStatement
}

------------------------------Expression------------------------------------
---------------------------------------------------------------------------

abstract sig Expr {
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

fun ExpOwnerSt [e:Expr] : Statement {
	e.owner + (e.^parent).owner
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
   all e: Expr | (not e in e.^children) && (e != e.parent)
}

fact LiteralNoChildren {
   all e: Expr | all l: Literal | e.parent != l
}

fact VariableReferenceNoChildren{
	all e: Expr | all v: VariableReference | e.parent != v
}

fact ParentsMatchChildren {
 all e1, e2: Expr | e2 in e1.children <=> e2.parent = e1
}

fact ParameterTypeMatch {
    all e: CallExpression | all t: e.calledFunction.parameters.type |
        # { p: e.calledFunction.parameters | p.type = t } = # { p: e.parameters | p.type = t}
}

fact CallExpressionMatchFunctionType{
	all c: CallExpression | c.calledFunction.returnType = c.type

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
--	all f: FormalParameter | f.type != none
}

fact FormalParametersAreDeclaredAndAssigned{
--	all f: FormalParameter | (isTrue[f.declared]) && (isTrue[f.assigned])
}

-------------------------------Variable-------------------------------------
---------------------------------------------------------------------------
sig Variable { 
	type: one Type
}

sig VariableReference extends Expr{
	reference: one Variable
}

sig VarDecl extends Statement{
	variable: one Variable
} 

fact ReferenceVariableTypeMatch{
	all v: Variable|all r: VariableReference | (r.reference = v => r.type = v.type)
}

fact WithoutAssignmentNoReference{
	all v: Variable| (not v in FormalParameter &&  some r: VariableReference | r.reference =v)  =>(some s:AssignmentStatement | s.var = v)
}

fact NeedsDeclarationStatement{
	all v: Variable | not v in FormalParameter => (some s:VarDecl | s.variable = v) 
}

fact NoParameterDeclaration{
	all s: VarDecl | not  s.variable in FormalParameter
}

fact NeedsAssignmentStatement{
	all v: Variable | not v in FormalParameter => (some s:AssignmentStatement | v = s.var )
}

fact NoParameterAssignment{
	all s:AssignmentStatement | not s.var in FormalParameter
}

fact CallExpressionNoRecursion{
	all c: CallExpression | not c in c.parameters
}

fact VarDeclNoExpr { 
	all s: VarDecl | s.expression = none 
}

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
 	t2 in t1.*parentType
}

pred p_assignsTo [s: Statement, vd: VarDecl] {
	vd.variable in s.var
}

/*
pred test{ 
	all u: Function | p_containsCall [u] 
	all v: Variable |p_isAssigned [v] 
	all v: Variable |p_isRead [v]
	all v: Variable| p_isDeclared [v] 

	all t1, t2: Type| p_subtypeOf [t1, t2]
	all s: Statement| all vd: VarDecl |p_assignsTo [s,vd] 
}
*/

---------------------------------------------------------------------------
-------------------------------Show----------------------------------------
---------------------------------------------------------------------------
pred show{}
run show for 3


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

/*
pred task3 {
	#AssignmentStatement =1
	#Variable = 1
	#Literal = 1
}


run task3 for 4

// Doesn't work
*/

/*
pred task4{
	#AssignmentStatement =1
	#CallExpression =1
	#Variable = 1
	all a: AssignmentStatement | some c: CallExpression | 
	(c = a.expression) && 
	(a.var.type != c.type) && // VariableType not CallExpressionType
	(c.calledFunction.returnType != c.calledFunction.lastStatement.expression.type) 

}

run task4 for 4
*/

/*
pred task5{
	#Literal = 1
	#Type = 2
	
	all disj t1, t2: Type | not p_subtypeOf [t1, t2] && not p_subtypeOf [t2, t1]

}

run task5 for 2
*/
