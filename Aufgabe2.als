

//------------------Project 1-------------------------------------
//---------------------------------------------------------------
//------------Philipp Schimmelfennig -Panuya Balasuntharam------------
//---------------------------------------------------------------

abstract sig LinearProgram{
	function: some Function,
	mainFunction: one MainFunction
}


--------------------------Type-------------------------------------

sig Type {
	superType: lone Type
}


sig Function {
	returnType: one Type, 
	returnValue: one ReturnStatement,
	formalParameter: set FormalParameter,
	belongsToOneLinPr: one LinearProgram, 
	returnStatements: some ReturnStatement,
	sequence: one  LinearSequenceOfStatement
}

sig MainFunction extends Function{

}


fact belongsToFunction{
	all f: Function | all l:LinearProgram | f.belongsToOneLinPr = l <=> l.function = f
}


fact avoidRecursion{
	
}

-------------------------Parameter--------------------------------

abstract sig Parameter {
	type: one Type
}

sig FormalParameter extends Parameter {
	belongsTo: one Function,
	belongsToOneVariable: one Variable
}

sig ActualParameter extends Parameter {}


fact reflexitivFormalParameter{
	all f: Function | all p: FormalParameter | f.formalParameter = p <=> p.belongsTo = f
}


--------------------------Statement-----------------------------

sig LinearSequenceOfStatement {
	belongsTo: one Function,
	firstStatement: one Statement,
	statements: some Statement
}

abstract sig Statement {
	nextStatement: lone Statement
}

sig AssignementStatement  extends Statement{
	variable: one DeclaredVariable,
	expressions: some Expr
}

sig ReturnStatement extends Statement{
	belongsTo:  one Function,
	isIn: one LinearSequenceOfStatement
}



fact returnStatementBelongsToOneFunction {
	all f: Function | all r: ReturnStatement| r. belongsTo = f <=> r in f.returnStatements
}


fact statement{
 	all s: LinearSequenceOfStatement |all x: Statement | x in s.statements <=> x in (s.firstStatement.^nextStatement + s.firstStatement)
} 


fact allStatementMustAppear{
	all a: AssignementStatement |all s: LinearSequenceOfStatement  |a in s.statements
}

fact noCircle{
	all s1, s2: Statement | s1.nextStatement = s2 => s1 not in s2.^nextStatement
}


fact noItSelf{
	all s:Statement | s.nextStatement != s
}

fact differentNextStatement {
	all s1, s2, s3: Statement | s1.nextStatement = s2 => s3.nextStatement != s2
}


------------------------------------------------------------------

sig Expr {
	type: one Type
}

sig Literal extends Expr {}

sig CallExpression {
	calledFunction: one Function
}

---------------------------Expression Tree-----------------------
sig Node {
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



-------------------------------Variable-----------------------------------------

sig Variable {
	declaredVariables: set DeclaredVariable,
	formalParameters: set FormalParameter, 
	assignedVariables: set AssignedVariable,
	belongsToOneFunction: one Function
}


sig DeclaredVariable {
	type: one Type,
	belongsTo: one Variable
	
}

sig AssignedVariable extends DeclaredVariable {
	readIn: some Expr,
}


sig VarDecl extends Statement{
	type: one Type
} // in UML we call it DeclarationStatement



fact variablelist{
	(all d: DeclaredVariable | all v: Variable | d in v.declaredVariables <=> d.belongsTo = v) &&
	(all p: FormalParameter | all v: Variable | p in v.formalParameters  <=> p.belongsToOneVariable = v) 
}



















//----------------------Functions--------------------------------


fun p_numFunctionCalls[]:Int {
	#CallExpression
}

/*fun p_expressionTypes[]:set Type {

}*/


/*
fun p_literalTypes[]:set Type {}
*/


/*
fun p_parameters[f:Function]:set FormalParameter {

}

*/










pred show {}

run show for 3
