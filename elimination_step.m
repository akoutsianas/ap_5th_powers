// We compute classical newforms using the Hilbert newforms package


function Hilbert_newforms(N)
        /*
        INPUT:
                - ``N`` : an integer

        OUTPUT:
                The space of classical newforms of level N as Hilbert newforms
        */

        QQ := RationalsAsNumberField();
        ZZ := Integers(QQ);
        M := HilbertCuspForms(QQ, N*ZZ);
        p := Min([p : p in PrimeFactors(N) | Valuation(N,p) eq 1]);
        A := QuaternionAlgebra(p*ZZ, InfinitePlaces(QQ) : Optimized);
        NewFs := NewSubspace(M : QuaternionOrder:=MaximalOrder(A));

        return  NewformDecomposition(NewFs);

end function;


function eliminate_newforms(k : Bound := 100, Newfs := [])
	/*
	INPUT:
		- ``k`` : 1,2,5 or 10.
		- ``Bound`` : an upper bound of the primes we use in the elimination step
		- ``Newfs`` : a list of new forms

	OUTPUT:
		A list of primes for which the eliminations step fails.
	*/


	// We compute the newforms if they are not given

	if #Newfs eq 0 then
		if k eq 1 then 
			Newfs := Hilbert_newforms(2^8 * 5^2 * 7);
		elif k eq 2 then
			Newfs := Hilbert_newforms(2 * 5^2 * 7);
		elif k eq 5 then
			Newfs := Hilbert_newforms(2^8 * 5 * 7);
		else
			Newfs := Hilbert_newforms(2 * 5 * 7);
		end if;
	
	end if;

	// We apply Proposition 3.1

	Maxn := 5;
	num := 0;	
	tHil := MakeType("ModFrmHil");
	small_primes := [2,3,5];
	i := 1;
	for fnew in Newfs do
		//print "i",i;
		if Type(fnew) eq tHil then
			ZZ := RingOfIntegers(BaseField(fnew));
			a3fnew := HeckeEigenvalue(Eigenform(fnew),3*ZZ);
		else
			a3fnew := Coefficient(fnew[1],3);
		end if;
		if Norm(a3fnew^2 - 16) ne 0 then
			Maxn := Max(Max(PrimeFactors(Integers()!(Norm(a3fnew^2 - 16)))),Maxn);
		end if;
		//print "a3fnew",a3fnew;
		if Max(PrimeFactors(Integers()!(Norm(a3fnew^2 - 16)))) gt 5 then
			Bfnews := [Integers()!(Norm(a3fnew^2 - 16))];
			for q in PrimesInInterval(11,Bound) do
				
				if Type(fnew) eq tHil then
					aqfnew := HeckeEigenvalue(Eigenform(fnew),q*ZZ);
				else
					aqfnew := Coefficient(fnew[1],q);
				end if;
				prod := q * Norm((aqfnew^2 - (q+1)^2));
				traces := [];

				for r in [0..Floor(Sqrt(q))] do
					prod *:= Norm((4*r^2 - aqfnew^2));
				end for;
				Append(~Bfnews,Integers()!prod);
				
			end for;
			g := GCD(Bfnews);
			if g ne 0 then
				if #PrimeFactors(g) gt 0 then
					//Maxn := Max(Max(PrimeFactors(g)),Maxn);
					if Max(PrimeFactors(g)) gt 5 then
						small_primes_fnew := [];
						print "Newform with index ",i;
						for n in [p : p in PrimeFactors(g) | p gt 5] do
							//print "i",i;
							if n eq 13 then
								num +:= 1;
							end if;
							if not Kraus_method(k,n,fnew) then
								Append(~small_primes_fnew,n);
								if n notin small_primes then
									Append(~small_primes,n);
								end if;
							end if;
						end for;
						if #small_primes_fnew gt 0 then
							printf "small primes = %o, i = %o\n",small_primes_fnew,i;
						end if;
					end if;
				end if;
			else
				print "We have a zero";
			end if;
		end if;
		i +:= 1;
	end for;

	//print "num",num,Maxn;
	return Sort(small_primes);
end function;




function Kraus_method(k,n,fnew : Bound := 5000)
	/*
	INPUT:
		- ``k`` : an integer equal to 1,2,5
		- ``n`` : an odd prime >= 7.
		- ``fnew`` : a newfor,

	OUTOUT:
		True, if Kraus method works for this exponent n, k and newform fnew. Otherwise, false.
	*/


	// Frey curve
	if k eq 5 then
		E := function(T,b) return EllipticCurve([0,4*T,0,2*b,0]); end function;
	elif k eq 1 then
		E := function(T,b) return EllipticCurve([0,20*T,0,10*b,0]); end function;
	elif k eq 2 then
		E := function(T,b) return EllipticCurve([1,(5*T-1)/4,0,5 * (b - 5*T^2)/2^6,0]); end function;
	end if;


	tHil := MakeType("ModFrmHil");
	for q in PrimesInInterval(11,Bound) do
		if (q - 1) mod n eq 0 then
			findq := true;
			
			if Type(fnew) eq tHil then
				ZZ := RingOfIntegers(BaseField(fnew));
				aqfnew := HeckeEigenvalue(Eigenform(fnew),q*ZZ);
			else
				aqfnew := Coefficient(fnew[1],q);
			end if;
			t := Integers()!((q-1)/n);
			GF := GF(q);
			_<x> := PolynomialRing(GF);
			An := [r[1] : r in Roots(x^t - 1)];
			A := 7*k^(4*n - 5);
	
			if Integers()!(Norm((q +1)^2 - aqfnew^2)) mod n eq 0 then
				findq := false;
			end if;

			for b in An do
				for a in An do
					s := Integers()!(10/k);
					T := Roots(s*x^2 - b - A*a^4);
					//print "T",T;
					if #T gt 0 then
						P := 1;
						for r in T do
							P *:= q + 1 - Order(E(r[1],b)) - aqfnew;
						end for;	
						
						if Integers()!(Norm(P)) mod n eq 0 then
							findq := false;
						end if;
					end if;
				end for;
			end for;
			if findq then
				printf "successful Kraus for n = %o and q = %o\n",n,q;
				return true;
			end if;
		end if;	
	end for;

	return false;
	

end function;


