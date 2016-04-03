//------------------Project 1------------------------------------------------
//-------------------------------------------------------------------------
//------------Philipp Schimmelfennig -Panuya Balasuntharam----------------------
//-------------------------------------------------------------------------


abstract sig Value {}
one sig True, False, Undefined extends Value {}

pred isTrue[b: Value] { b in True }

pred isFalse[b: Value] { b in False }

pred isUndef[b: Value] { b in Undefined}

--------------------------------------------------------------------------
sig LinearProgram{
	functions: some Function,
	mainFunction: one Function
}

fact {
	#LinearProgram = 1
}

----------------------------Function----------------------------------------
---------------------------------------------------------------------------
sig Function {
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

-------------------------------------------------------------------------

fact CalledOnce{
	all f: Function | #{e: CallExpression| e.calledFunction = f} <= 1
}


-----------------------------Execution--------------------------------------
---------------------------------------------------------------------------

sig Execution{ 
	evalVar: Statement -> Variable -> lone Value,
	evalExpr: Expr -> lone Value
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

------------------------------Expression------------------------------------
---------------------------------------------------------------------------

abstract sig Expr {
   children: set Expr,
   parent: lone Expr,
   owner: lone Statement,
   isParameter: one Value
}

sig Literal extends Expr {
	value: one Value
}

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


-------------------------------------------------------------------------
sig And extends Expr{}

sig Not extends Expr{}

fact BinaryAnd{
	all a: And | #a.children = 2
}

fact UnaryNot{
	all n: Not | #n.children = 1
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
sig Variable {}

sig VariableReference extends Expr{
	reference: one Variable
}

 
fact WithoutAssignmentNoReference{
	all v: Variable| (not v in FormalParameter &&  some r: VariableReference | r.reference =v)  =>(some s:AssignmentStatement | s.var = v)
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

---------------------------------------------------------------------------
//----------------------Functions------------------------------------------
-------------------------------------------------------------------------

fun p_numFunctionCalls[]: Int {
 	# CallExpression
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

pred p_isParameter[v:Variable]{
	some f: Function | v in f.parameters
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
------------------------------- Task D - Functions —-------------------------
---------------------------------------------------------------------------

fun  p_val[e:Execution,p:Expr]:Value {
	p.(e.evalExpr)
}

fun p_numNot[]:Int {
	#Not
}

/*
fun p_retval[e:Execution,f:Function]:Value {}


fun p_argval[e:Execution,f:Function,p:FormalParameter]:Value{}



fun p_valbefore[e:Execution, s:Statement, v:Variable] : Value {}

*/
