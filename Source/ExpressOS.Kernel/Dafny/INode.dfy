class Data {}
class INode 
{
ghost var tailContents: seq<Data>;
ghost var footprint: set<INode>;

var data: Data;
var next: INode;

/*
function len():int
requires Valid();
reads this, footprint;
ensures len() == |footprint| == |tailContents| + 1;
{
if next == null then 1 else 1 + next.len()
}
*/

predicate good()
reads this, footprint;
{
    this in footprint 
	&& (next != null ==> (next in footprint 
	&& this !in next.footprint 
	&& footprint == {this} + next.footprint
	&& tailContents == [next.data] + next.tailContents
	))
	&& (next ==null ==> tailContents == [] && footprint == {this})
}

predicate Valid()
reads this, footprint;
{
    good() && (next != null ==> next.Valid())
}

/*
predicate ValidLemma()
requires Valid();
reads this, footprint;
ensures ValidLemma();
ensures forall nd :: nd in footprint ==> nd != null &&
										nd.footprint <= footprint;
{
if next == null then (footprint == {this})
else (
footprint == {this} + next.footprint
&& next.ValidLemma())
}

predicate allVLemma()
requires Valid();
reads this, footprint;
ensures allVLemma();
ensures forall nd :: nd in footprint ==> nd != null && nd.Valid();
{
next != null ==> next.allVLemma()
}
*/

/*
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
*/

////////////////////////////////////////////////////////

method update(d:Data, index:int)
requires 0 <= index <= |tailContents|;
requires Valid();
modifies footprint;
ensures Valid();
ensures index == 0 ==> (data == d && tailContents == old(tailContents));
ensures index > 0 ==> (this.data == old(this.data)
&& tailContents == old(tailContents[0..index-1]) + [d] +
						old(tailContents[index..]));
ensures footprint == old(footprint);
{
if (index == 0) {data := d; }
else {
next.update(d, index-1);
tailContents := [next.data] + next.tailContents;
}

}


}


