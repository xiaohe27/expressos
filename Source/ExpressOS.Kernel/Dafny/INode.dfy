class Data {}
class INode 
{
ghost var tailContents: seq<Data>;
ghost var footprint: set<INode>;

var data: Data;
var next: INode;


function len():int
requires Valid();
reads this, footprint;
ensures len() == |footprint| == |tailContents| + 1;
{
if next == null then 1 else 1 + next.len()
}


predicate good()
reads this, footprint;
{
    this in footprint 
	&& (next != null ==> (next in footprint 
	&& this !in next.footprint 
	&& next.footprint + {this} == footprint
	))
	&& (next ==null ==> tailContents == [] && footprint == {this})
	&& (next != null ==> tailContents == [next.data] + next.tailContents)
}

predicate Valid()
reads this, footprint;
{
    this in footprint 
	&& (next != null ==> (next in footprint 
	&& this !in next.footprint 
	&& next.footprint + {this} == footprint
	&& next.Valid()
	))
	&& (next ==null ==> tailContents == [] && footprint == {this})
	&& (next != null ==> tailContents == [next.data] + next.tailContents)
}

predicate ValidLemma()
requires Valid();
reads this, footprint;
ensures Valid();
ensures forall nd :: nd in footprint ==> nd != null && nd.footprint <= footprint;
ensures forall nd :: nd in footprint - {this} ==> this !in nd.footprint;
{
next != null ==> (next.ValidLemma())
}


constructor init(d:Data) 
modifies this;
ensures Valid();
ensures data == d;
ensures next == null;

ensures footprint == {this};
ensures tailContents == [];
ensures fresh(footprint - {this});
{
    data := d;
	next := null;
    tailContents := [];
	footprint := {this};
}

method preAppend(d:Data) returns (node:INode)
requires Valid();
ensures node != null && node.Valid();
ensures node.data == d && node.next == this;
ensures node.tailContents == [this.data] + this.tailContents;
{
var r := new INode.init(d);
r.next := this;

r.footprint := r.footprint + this.footprint;
r.tailContents := [this.data] + this.tailContents;
return r;
}

method append(d:Data)
requires Valid();

modifies footprint;
decreases footprint;
ensures Valid();
ensures (tailContents == old(tailContents) + [d]);
ensures this.data == old(this.data);
ensures fresh(footprint - old(footprint));
{
var node := new INode.init(d);

if(next == null)
{
next := node;
this.tailContents := [d];
}

else
 {
next.append(d);
this.tailContents := [this.next.data] + this.next.tailContents;
}

this.footprint := {this} + next.footprint;

}

method insertAt(i:int, d:Data)
requires 0 < i <= |tailContents|;
requires Valid();
modifies footprint;
ensures Valid();
ensures this.data == old(this.data);
ensures tailContents == old(tailContents[0..i-1]) + [d] + old(tailContents[i-1..]);
ensures fresh(footprint - old(footprint));
{
var newNd := new INode.init(d);

if (i == 1) {
newNd.next := next;
newNd.tailContents := tailContents;
newNd.footprint := {newNd} + next.footprint;

assert newNd.tailContents == old(tailContents[i-1..]);
assert newNd.Valid();

this.next := newNd;
}

else {
next.insertAt(i-1, d);
}

this.tailContents := [next.data] + next.tailContents;

assert tailContents == old(tailContents[0..i-1]) + [d] + old(tailContents[i-1..]);

this.footprint := {this} + next.footprint;
}


////////////////////////////////////////////////////////

function getFtprint(nd:INode): set<INode>
reads nd;
{
if nd == null then {} else nd.footprint
}

function sumAllFtprint(mySeq: seq<INode>): set<INode>
reads mySeq;
ensures forall nd :: nd in mySeq ==> 
	(nd != null ==> nd.footprint <= sumAllFtprint(mySeq));
{
if mySeq == [] then {} else getFtprint(mySeq[0]) + sumAllFtprint(mySeq[1..])
}

function method getSeq(nd:INode): seq<INode>
requires nd != null && nd.Valid();
reads nd, getFtprint(nd);
ensures forall node :: node in getSeq(nd) ==> node != null && node.Valid();
ensures (set node | node in getSeq(nd)) == nd.footprint;
ensures forall i :: 0 <= i < |getSeq(nd)| - 1 ==> 
		getSeq(nd)[i].next == getSeq(nd)[i+1];
ensures getSeq(nd)[|getSeq(nd)|-1].next == null;
{
if nd.next == null then [nd] else [nd] + getSeq(nd.next)
}

}


