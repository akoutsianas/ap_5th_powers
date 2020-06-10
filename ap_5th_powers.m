/////// We study the equation (x-d)^5 + x^5 + (x+d)^5 = y^p //////




// Case n = 3

function torsion_Picard()
	/*
	We prove that the order of the torsion subgroup is one.
	*/

	A<x,y> := AffineSpace(Rationals(),2);
	C := Curve(A,y^3 - ( x^4 + 200*5^2*x^2 + 3000*5^4));

	order := Evaluate(Numerator(ZetaFunction(ChangeRing(C,GF(11)))),1);

	for q in PrimesInInterval(13,50) do
		order := GCD(order,Evaluate(Numerator(ZetaFunction(ChangeRing(C,GF(q)))),1));
	end for;
	

	return order;
end function;


function case_n_3_k_5()
	/*
	We determine the set of rational points of the Picard curve for n = 3 and k = 5. Firstly, we should run the Magma
	files "coleman.m" and "colemanextensions.m".
	*/

	f := y^3 - (x^4 + 200*5^2*x^2 + 3000*5^4);
	data := coleman_data(f,19,200);
	g := x^2 + 1500;
	Qdivs := Q_divs(data,1000,g);
	L,v := effective_chabauty_with_Qdiv(data : Qpoints := Qdivs, e := 200);

	return L,v;

end function;




// Case n = 5


// Using elliptic curves over K(7^1/5)


function ChabautyBirational(C,P,GensE)
	/*
	INTPUT:
		- ``C`` : a hyperelliptic genus one curve of the form
		- ``P`` : a rational point on C
		- ``GenE`` :  generators of a finite index subgroup of the birational to C elliptic curve E.

	OUTPUT:
		
	*/

	E<X,Y,Z> := Curve(GensE[1]);

	f := HyperellipticPolynomials(C);
	x := Parent(f).1;
	K := BaseRing(f);
	P1 := ProjectiveSpace(Rationals(),1);
	x0 := P[1];	

	f := Evaluate(f,x + x0);
	coef := Coefficients(f);

	a := coef[5];
	b := coef[4];
	c := coef[3];
	d := coef[2];
	q := P[2];

	G := AbelianGroup([Order(g) : g in GensE]);
	

	if not IsZero(q) then

		ChabMWtoE := map<G -> E | x :-> &+[Eltseq(x)[i]*GensE[i] : i in [1..#GensE]]>;//return ChabMWtoE;
		Ecov := map<E -> P1 | [x0*Y + (2*q*(X + c*Z) - d^2*Z/(2*q)),Y]>;

		V,R := Chabauty(ChabMWtoE,Ecov);

		for p in PrimeFactors(R) do
			if Saturation(GensE,p) ne GensE then
				print "Problem with saturation at prime ",p;
			end if;
		end for;

		sols := [];
		for P in V do
			X0 := Rationals()!Ecov(ChabMWtoE(P))[1];
			if IsSquare(X0^5 + 7*10^5) and X0 notin sols then
				Append(~sols,X0);
			end if;
		end for;
	end if;

	return sols;

end function;


function no_points_homogeneous_space(C,J,GensJ : Bound := 10)
	/*
	INPUT:
		- ``C`` : a genus one curve of the form y^2 = f(x) where f is a quartic polynomial
		- ``J`` : the Jacobian of ``C``
		- ``GensJ`` : a set of generators of a full rank subgroup of J that is 2-saturated

	OUTPUT:
		True if there is not point on C, otherwise false.
	*/
	

	for v in CartesianPower([0,1],#GensJ) do
		P := &+[GensJ[i]*v[i] : i in [1..#GensJ]];
		if IsIsomorphic(C,TwoCover(P)) then
			return false;
		end if;
	end for;	

	return true;
end function;



