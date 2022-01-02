class MontgomeryCurveFp2(object):
    def __init__(self,field, coef1, coef2):
        self._field = field
        self._coef1 = coef1
        self._coef2 = coef2
        self._prime = field.characteristic()
        self._size = self._prime^2
        self._discriminant = self._coef2 * (self._coef1^2 - 4)
    def __repr__(self):
        s = "Montgomery elliptic curve defined by "
        #----------------------------------------------
        if (self._coef2 == 1):
            s += "y^2 = x^3 + "
        else:
            s += "(%s)*y^2 = x^3 + "%self._coef2
        #----------------------------------------------   
        if (self._coef1 == 0):
            s += "x "
        elif (self._coef1 == 1):
            s += "x^2 + x "
        else:
            s += "(%s)*x^2 + x "%self._coef1
        s += " over finite field of size %s^2."%self._prime
        return s
    
    def __eq__(self, other):
        return (self._field, self._coef1, self._coef2) == (other._field, other._coef1, other._coef2)
    def __call__(self, *arg,**kwarg):
        R = self._field
        if (len(arg) == 1):
            if arg[0] == 0:
                return PointMCFp2(R(0),R(1),R(0), self)
            else:
                return PointMCFp2(R(arg[0]), R(self.lift_x(arg[0]).y()), 1, self)
    def coef1(self):
        return self._coef1
    def coef2(self):
        return self._coef2
    def field(self):
        return self._field
    def j_invariant(self):
        #SIKE official document, Algorithm 9
        R = self._field
        A = self._coef1
        j = A^2
        t0 = j - 2
        t0 = t0 - 1
        j = t0 - 1
        t0 = t0 + t0
        t0 = t0 + t0
        t1 = t0^2
        t0 = t0 * t1
        t0 = t0 + t0
        t0 = t0 + t0
        j = R(1/j)
        j = t0 * j
        return R(j)
  
    ##################################################
    # general
    ##################################################
    
    def discriminant(self):
        return self._discriminant
    
    #function
    def is_Mont_EC(self):
        if (self._discriminant == 0):
            return False
        else:
            return True
                   
    def is_x_coord(self, x):
        R = self._field
        if (R((x^3 + self._coef1 * x^2 + x)/self._coef2).is_square()):
            return True
        else:
            return False
        
    def is_point(self, point):
        R = self._field
        x = point._x
        point = point.transformZ()
        if self.is_x_coord(point._x):
            return R((x^3 + self._coef1 * x^2 + x)/self._coef2).sqrt() == point._y or R((x^3 + self._coef1 * x^2 + x)/self._coef2).sqrt() == -point._y
        else:
            return False
        
    def twist(self):
        R = self._field
        a = 1
        while (R(a).is_square()):
            a = R.random_element()
        return MontgomeryCurveFp2(self._field, R(self._coef1), R(a)*R(self._coef2))
    
    #def points_x(self):
    #    R = self._field
    #    points = [R(x) for x in range(0, self._prime) if self.is_x_coord(x)]
    #    #print(points)
    #    return points
    
    def lift_x(self, x, MF = False, all = False):
        if not self.is_x_coord(x):
            raise ValueError("No point with x = %s on this curve"%x)
        else:
            R = self._field
            y = R((x^3 + self._coef1 * x^2 + x)/self._coef2).sqrt()
            if (MF == True):
                return PointMCFp2(R(x), None, 1, self)
            else: 
                if (all == False):        
                    return PointMCFp2(R(x), R(y), 1, self)
                else:
                    return PointMCFp2(R(x), R(y), 1, self), PointMCFp2(R(x), R(-y), 1, self)
                              
    def random_point(self, MF = False):
        r"""
        This algorithm generates random point on some elliptic curve, this point has order different from 2 (and 1). There is a lot of algorithms that want this point to have order different from 2.
        """
        R = self._field
        z = R.gen()
        help1 = False
        x = ZZ.random_element(self._prime)*z + ZZ.random_element(self._prime)
        while not (self.is_x_coord(x)):
                x = ZZ.random_element(self._prime)*z + ZZ.random_element(self._prime)
        if (MF == False):
            return self.lift_x(x, MF = False, all = False)
        else:
            return self.lift_x(x, MF = True, all = False)
        
    def findKernel(self, k, P, Q, PdiffQ):
        #Montgomery three-point ladder
        #SIKE official document, Algorithm 8
        """
        This algorithm computes point P1 = P + k*Q.
        """
        R = self._field
        if not(isinstance(k, list) or isinstance(k,str)):
            k = Integer(k)
            k = k.digits(2)
        if (isinstance(k, list) or isinstance(k,str)):
            l = len(k)
            P0 = Q
            P1 = P
            P2 = PdiffQ
            for i in range(0, l):
                if (k[i] == 0):
                    (P0,P2) = P0.dblAdd(P2,P1)
                else:
                    (P0, P1) = P0.dblAdd(P1,P2)
            return P1
        
    def Montgomery2Weierstrass(self):
        F = self._field
        A = self._coef1
        B = self._coef2
        a = 1/(B^2) - A^2/(3*B^2)
        b = - A^3/(27*B^3) - a*A/(3*B)
        return EllipticCurve(F,[a,b])
    
    def pointM2W(self,Q):
        r"""
        Fuction made for conversion between SWF of EC and MF of EC.
        """
        F = self._field
        p = self._prime
        A = self._coef1
        B = self._coef2
        x = F((Q._x + A/3)/B)
        y = F(Q._y/B)
        E = self.Montgomery2Weierstrass()
        return E(x,y)
        
    def isogenyMF(self, point, l):
        r"""
This algorithm computes the coef of E': y2 = x3 + Bx2 + x, which is l-isogenous with E: y2 = x3 + Ax2 + x
#formula B = PI(A - 3*SI), where PI is product of x-coord. of all points in <K> (except onfinity), and SI is sum over all points in <K> (except infinity) of (x-coord - 1/x-coord.)     
        """
        R = self._field
        PI = R(point._x)
        SI = R(point._x - 1/point._x)
        for i in range(2,l):
            point1 = point.mLadder(i)
            PI = PI * point1._x
            SI = SI + R(point1._x - (1/point1._x))
            
        return IsogenyBSIDH(domain = self, codomain = MontgomeryCurveFp2(R,R(PI*(self._coef1 - 3*SI)),self._coef2), kernel = point, baseDegree = l, exponent = 1)
    
    def isogenyEF(self, point, l):
        r"""
This functions compute coef B of E', which is l-isogeny to self, using arithmetic on Edward curves.
        """
        R = self._field
        a = R((self._coef1 + 2 )/self._coef2)#tranformation from MF to EF
        d = R((self._coef1 - 2)/self._coef2)
        M = 1
        N = 1
        s = (l - 1)//2
        for i in range(1, s + 1):
            point1 = point.mLadder(i)
            Y = (point1._x - point1._z)
            T = (point1._x + point1._z)
            M = R(M*Y)
            N = R(N*T)
            
        aNew = R((a^l)*(N^8))
        dNew = R((d^l)*(M^8))
        
        return IsogenyBSIDH(domain = self, codomain = MontgomeryCurveFp2(R,R(2*(aNew + dNew)/(aNew - dNew)),4/(aNew - dNew)), kernel = point, baseDegree = l, exponent = 1)
    ########################################################################
    # SIKE
    ########################################################################
    def isogeny2(self, kernel):
        #SIKE official document, Algorithm 11
        r"""
This algorithm computes the coefficient of E': y2 = x3 + Ax2 + x, which is 2-isogenous with E: y2 = x3 + A'x2 + x (kernel = kernel).
        """
        R = self._field
        AA = kernel._x^2
        CC = kernel._z^2
        AA = CC - AA
        C = R(CC/4)
        A = AA - 2*C
        A = R(A/C)
        return IsogenySIKE2(domain = self, codomain = MontgomeryCurveFp2(R, A, self._coef2), kernel = kernel, exponent = 1)      
    
    
    def isogeny3(self, kernel):
        #SIKE official document, Algorithm 15
        """
This algorithm computes the coefficient of E': y2 = x3 + Ax2 + x, which is 3-isogenous with E: y2 = x3 + A'x2 + x (kernel = kernel).
        """
        R = self._field
        K1 = kernel._x - kernel._z
        t0 = K1^2
        K2 = kernel._x + kernel._z
        t1 = K2^2
        t2 = t0 + t1
        t3 = K1 + K2
        t3 = t3^2
        t3 = t3 - t2
        t2 = t1 + t3
        t3 = t3 + t0
        t4 = t3 + t0
        t4 = t4 + t4
        t4 = t1 + t4
        AA = t2 * t4
        t4 = t1 + t2
        t4 = t4 + t4
        t4 = t0 + t4
        A = t3 * t4
        
        coef1 = R((A + AA)/2)
        coef2 = R((A - coef1)/2)
        A = R(coef1/coef2)
        return IsogenySIKE3(domain = self, codomain  = MontgomeryCurveFp2(R,R(A),self._coef2), kernel = kernel, exponent = 1)
    
    def isogeny4(self, kernel):
        #SIKE official document, Algorithm 13
        r"""
This algorithm computes the coefficient of E': y2 = x3 + Bx2 + x, which is 4-isogenous with E: y2 = x3 + Ax2 + x (kernel = kernel).
        """
        R = self._field
        k2 = kernel._x - kernel._z
        k3 = kernel._x + kernel._z
        k1 = (kernel._z)^2
        k1 = k1 + k1
        CC = k1^2
        k1 = k1 + k1
        AA = kernel._x^2
        AA = AA + AA
        AA = AA^2
        C = R(CC/4)
        A = AA - 2*C
        A = R(A/C)
        return IsogenySIKE4(domain = self, codomain = MontgomeryCurveFp2(R,A,self._coef2), kernel = kernel, exponent = 1)
    
    def isogenyDecompose2(self, kernel, expo, P, Q, PdiffQ):
        ##napsano podle definice dekompozice isogenie
        """
        Decompose isogeny of order 2^e into isogenies of order l
        
        
        input: l... small prime number 
               e... natural number (exponent)
               E... EC
               A... point of order 2^e, generating kernel
               points... we need images of certain point, this is list of these points 
        output:Eh... codomain of isogeny with kernel <A>
               points... list of images
        """
        E = self
        EE = self
        A = kernel
        Kernel = kernel
        for i in range(1,expo + 1):
            kernel = A.dbl_eA(expo - i)
            phiA = E.isogeny2(kernel)
            E = phiA.codomain()
            A = phiA(A)
            P = phiA(P)
            Q = phiA(Q)
            PdiffQ = phiA(PdiffQ)
        return IsogenySIKE2(EE, E, kernel = Kernel, exponent = expo), P, Q, PdiffQ
    
    def isogenyDecompose3(self, kernel, expo, P, Q, PdiffQ):
        ##napsano podle definice dekompozice isogenie
        """
        Decompose isogeny of order 3^e into isogenies of order l
        
        
        input: l... small prime number 
               e... natural number (exponent)
               E... EC
               A... point of order 3^e, generating kernel
               points... we need images of certain point, this is list of these points 
        output:Eh... codomain of isogeny with kernel <A>
               points... list of images
        """
        E = self
        B = kernel
        Kernel = kernel
        for i in range(1,expo + 1):
            kernel = B.tpl_eB(expo - i)
            phiB = E.isogeny3(kernel)
            E = phiB.codomain()
            B = phiB(B)
            P = phiB(P)
            Q = phiB(Q)
            PdiffQ = phiB(PdiffQ)
        return IsogenySIKE3(self, E, kernel = Kernel, exponent = expo), P, Q, PdiffQ
    
    def isogenyDecompose4(self, kernel, expo, P, Q, PdiffQ):
        ##napsano podle definice dekompozice isogenie
        """
        Decompose isogeny of order 2^e into isogenies of order l
        
        
        input: l... small prime number 
               e... natural number (exponent)
               E... EC
               A... point of order 2^e, generating kernel
               points... we need images of certain point, this is list of these points 
        output:Eh... codomain of isogeny with kernel <A>
               points... list of images
        """
        E = self
        EE = self
        exponent = expo//2
        A = kernel
        Kernel = kernel
        for i in range(1,exponent + 1):
            kernel = A.dbl_eA(2*(exponent - i))
            phiA = E.isogeny4(kernel)
            E = phiA.codomain()
            A = phiA(A)
            P = phiA(P)
            Q = phiA(Q)
            PdiffQ = phiA(PdiffQ)
        if not (exponent * 2 == expo):
            kernel = A
            phiA = E.isogeny2(kernel)
            E = phiA.codomain()
            A = phiA(A)
            P = phiA(P)
            Q = phiA(Q)
            PdiffQ = phiA(PdiffQ)
        return IsogenySIKE2(EE, E, kernel = Kernel, exponent = expo), P, Q, PdiffQ
    
     
    
    ########################################################################
    # BSIDH
    ########################################################################
    
    def lift_xBSIDH(self, x):
        """
Use to construct a point "on" self with x-coordinate x, which is actualy on twist of self.
        """
        R = self._field
        return PointMCFp2(R(x), None, 1, self)
    
    def isogenyDecomposeBSIDH2(self, kernel, expo, points):
        ##napsano podle definice dekompozice isogenie
        """
        Decompose isogeny of order 2^e into isogenies of order l.
        
        input: kernel... point of order 2^e, generating kernel
               expo... natural number (exponent)
               points... we need images of certain point, this is list of these points 
        output:phi... isogeny with kernel <kernel>
               points... list of images
        """
        E = self
        KK = kernel
        K = kernel
        pointsHelp = []
        if points != []:
            for i in range(1,expo + 1):
                kernel = K.dbl_eA(expo - i)
                phiA = E.isogeny2(kernel)
                E = phiA.codomain()
                K = phiA(K)
                for P in points:
                    imageP = phiA(P)
                    pointsHelp.append(imageP)
                points = copy(pointsHelp)
                pointsHelp = []
            return IsogenySIKE2(self, E, kernel = KK, exponent = expo), points
        else:
            for i in range(1,expo + 1):
                kernel = K.dbl_eA(expo - i)
                phiA = E.isogeny2(kernel)
                E = phiA.codomain()
                K = phiA(K)
            return IsogenySIKE2(self, E, kernel = KK, exponent = expo)
            
    
    def isogenyDecomposeBSIDH(self, kernel, primes, points):
        """Decompose isogeny of order (odd) p1 * p2 * p3 * .... into isogenies of order p_i
                input: p_i... small odd prime number 
                kernel... point of order product(primes)
                points... we need images of certain point, this is list of these points 
         output:phiB... isogeny with kernel <kernel>
                points... list of images
        """
        E = self
        domain = self           
        ORDER = product(primes)
        order = product(primes)
        l = len(primes)
        imageKernel = kernel
        pointsHelp = []
        if points != []:
            for i in range(0,l):
                m = order//primes[l-1-i]
                B = imageKernel.mLadder(m)
                phiB = E.isogenyMF(B, primes[l-1-i])
                E = phiB.codomain()
                imageKernel = phiB(imageKernel)
                for P in points:
                    imageP = phiB(P)
                    pointsHelp.append(imageP)
                points = copy(pointsHelp)
                pointsHelp = []
                order = m
            return IsogenyBSIDH(domain = domain, codomain = E, kernel = kernel, baseDegree = ORDER, exponent = 1), points
        else:
            for i in range(0,l):
                m = order//primes[l-1-i]
                B = imageKernel.mLadder(m)
                phiB = E.isogenyMF(B, primes[l-1-i])
                E = phiB.codomain()
                imageKernel = phiB(imageKernel)
                order = m
            return IsogenyBSIDH(domain = domain, codomain = E, kernel = kernel, baseDegree = ORDER, exponent = 1)
    
    def isogenyDecomposeBSIDH_test(self,L, GB ,points):
        """Decompose isogeny of order (odd) p1 * p2 * p3 * .... into isogenies of order p_i
                input: p_i... small odd prime number 
                GB... point of order product(primes)
                points... we need images of certain point, this is list of these points 
         output:phiB... isogeny with kernel <GB>
                points... list of images
        """
        Eh = self
        domain = self    
        order = 1
        fl = list(factor(L))
        for i in fl:
            order = order * i[0]^i[1]
        ORDER = order
        imageGB = GB
        pointsHelp = []
        while order % 2 == 0:
            k = order // 2
            Bh = imageGB.mLadder(k)
            phiBh = Eh.isogeny2(Bh)
            Eh = phiBh.codomain()
            imageGB = phiBh(imageGB)
            for P in points:
                imageP = phiBh(P)
                pointsHelp.append(imageP)
            points = copy(pointsHelp)
            pointsHelp = []
            order = k
        
        l = len(fl)
        for i in range(0,l - ((ORDER + 1) % 2)):
            p = fl[l-i - 1][0]
            ex = fl[l-i - 1][1]
            for i in range(1,ex + 1):
                m = order//p
                Bh = imageGB.mLadder(m)
                phiBh = Eh.isogenyMF(Bh, p)
                Eh = phiBh.codomain()
                imageGB = phiBh(imageGB)
                for P in points:
                    imageP = phiBh(P)
                    pointsHelp.append(imageP)
                points = copy(pointsHelp)
                pointsHelp = []
                order = m
                    
        return phiBh, points
    
    def pointGivenOrderBSIDH(self, L):
        """
        Find point of given order different from 1 on EC E.
             input: L... order
             output: G... point on E of order L
        Construct for searching kernel of order L = 2^e in BSIDH.
        """
        F = self._field
        p = self._prime
        EW = EllipticCurve(F, [0,self._coef1/self._coef2,0,1/(self._coef2)^2,0])
        g = 1 #number different of L
        while not(g == (L)):
            G = EW.random_point() #taking random point from E
            g = G.order()
            if (g % (L) == 0):
                G = (g//(L))*G
                g = G.order()
                
    
        x = G[0]
        if not self._coef2 == 1:
            x = self._coef2 * x
        G = self.lift_x(x)
        return G
    
    def pointGivenOrderBSIDH2(self, L):
        """
        Find point of given order different from 1 on EC E.
             input: L... order
             output: G... point on E of order L
        Construct for searching kernel of order L = product(primes) in BSIDH.
        """
        F = self._field
        E = self
        p = self._prime
        
        if L < p - 1:
            P = E.random_point()
            kandidat2 = P.mLadder(L)
        
            while kandidat2._z == 0:
                P = E.random_point()
                kandidat2 = P.mLadder(L)
            k = (p-1)//(product(L.prime_factors()))
        
            for subsets in Combinations(factors(k)):
                l = 1
                kandidat = kandidat2
                for i in subsets:
                    kandidat = kandidat.mLadder(i)
                    l = l*i
                    if kandidat._z == 0:
                        break
            G = P.mLadder(l)
        else:
            G = E(0)
            while G._z == 0:
                P = E.random_point()
                for i in factors(L):
                    G = P.mLadder(i)
                    if G._z == 0:
                        break
            G = P   
        G = E.lift_x(G._x)
        return G
    
    def findKernelBSIDH_test2(self, m, L):
        D = self.lift_x(0)
        while D._x == 0:
            P = self.pointGivenOrderBSIDH_test(L)
            Q = self.pointGivenOrderBSIDH_test(L)
            G = Q.mLadder(m, False) + P
            D = G.mLadder(L//2)
        return G, P, Q
    
    def findKernelBSIDH_test(self, m, L):
        D = self(0)
        list1 = prime_factors(L)
        while D._z == 0:
            P = self.pointGivenOrderBSIDH_test(L)
            Q = self.pointGivenOrderBSIDH_test(L)
            G = Q.mLadder(m, False) + P
            D = G.mLadder(L//list1[0])
        return G, P, Q
    
    def pointGivenOrderBSIDH_test(self, L):
        import random
        """
        Find point of given order different from 1 on EC E.
             input: L... order
             output: G... point on E of order L
        Construct for searching kernel of order L = 2^e in BSIDH.
        """
        F = self._field
        p = self._prime
        EE = EllipticCurve(F,[0,self._coef1/self._coef2, 0, 1/(self._coef2)^2,0])
        O = EE(0)
        f = list(factor(L))
        P = self(0)
        k = 0
        for sub in f:
            if sub[0] > 17:
                k = 1
                break
            elif sub[1] > 1:
                Q = self.pointGivenOrderBSIDH(sub[0]^sub[1])
            else:
                r = random.sample(O.division_points(sub[0])[2::],1)
                x = r[0][0]
                if not self._coef2 == 1:
                    x = self._coef2 * x
                Q = self.lift_x(x)
            P = P + Q
        if k == 1:
            prod = 1
            for t in f:
                if sub[0] <= t[0]:
                    prod = prod * t[0]^t[1]
            Q = self.pointGivenOrderBSIDH2(prod)
            P = P + Q
        return P
    
    
    ########################################################################
    # eSIDH
    ########################################################################
    
   
    def isogenyDecomposeESIDH3(self, kernel, expo,points):
        ##napsano podle definice dekompozice isogenie
        """
        Decompose isogeny of order 3^e into isogenies of order 2
        
        
        input: kernel... point of order 3^e, generating kernel
               expo... natural number (exponent)
               points... we need images of certain point, this is list of these points 
        output:phi... isogeny with kernel <kernel>
               points... list of images
        """
        E = self
        B = kernel
        Kernel = kernel
        pointsHelp = []
        for i in range(1,expo + 1):
            kernel = B.tpl_eB(expo - i)
            phiB = E.isogeny3(kernel)
            E = phiB.codomain()
            B = phiB(B)
            for P in points:
                imageP = phiB(P)
                pointsHelp.append(imageP)
            points = copy(pointsHelp)
            pointsHelp = []
        return IsogenySIKE3(self, E, kernel = Kernel, exponent = expo), points
    
    
    def isogenyDecomposeESIDH4(self, kernel, expo,points):
        ##napsano podle definice dekompozice isogenie
        """
        Decompose isogeny of order 4^e into isogenies of order l
        
        
        input: kernel... point of order 4^e, generating kernel
               expo... natural number (exponent)
               points... we need images of certain point, this is list of these points 
        output:phi... isogeny with kernel <kernel>
               points... list of images
        """
        E = self
        B = kernel
        Kernel = kernel
        pointsHelp = []
        for i in range(1,expo + 1):
            kernel = B.mLadder(4^(expo - i))
            phiB = E.isogeny4(kernel)
            E = phiB.codomain()
            B = phiB(B)
            for P in points:
                imageP = phiB(P)
                pointsHelp.append(imageP)
            points = copy(pointsHelp)
            pointsHelp = []
        return IsogenySIKE4(self, E, kernel = Kernel, exponent = expo), points
    
    def isogenyDecomposeESIDH5(self, kernel, expo,points):
        ##napsano podle definice dekompozice isogenie
        """
        Decompose isogeny of order 5^e into isogenies of order l
        
        
        input: kernel... point of order 5^e, generating kernel
               expo... natural number (exponent)
               points... we need images of certain point, this is list of these points 
        output:phi... isogeny with kernel <kernel>
               points... list of images
        """
        E = self
        B = kernel
        Kernel = kernel
        pointsHelp = []
        for i in range(1,expo + 1):
            kernel = B.mLadder(5^(expo - i))
            phiB = E.isogenyMF(kernel,5)
            E = phiB.codomain()
            B = phiB(B)
            for P in points:
                imageP = phiB(P)
                pointsHelp.append(imageP)
            points = copy(pointsHelp)
            pointsHelp = []
        return IsogenySIKE5(self, E, kernel = Kernel, exponent = expo), points

###################################################
###################################################
###################################################
    
def isogenyDecompose4(kernel, expo, P, Q, PdiffQ):
        ##napsano podle definice dekompozice isogenie
        """
        Decompose isogeny of order 2^e into isogenies of order l
        
        
        input: l... small prime number 
               e... natural number (exponent)
               E... EC
               A... point of order 2^e, generating kernel
               points... we need images of certain point, this is list of these points 
        output:Eh... codomain of isogeny with kernel <A>
               points... list of images
        """
        
        exponent = expo//2
        A = kernel
        Kernel = kernel
        for i in range(1,exponent + 1):
            kernel = A.dbl_eA(2*(exponent - i))
            A = isogeny4_call(A, kernel)
            P = isogeny4_call(P, kernel)
            Q = isogeny4_call(Q, kernel)
            PdiffQ = isogeny4_call(PdiffQ, kernel)
        return A, P, Q, PdiffQ    
    
def isogeny4_call(point, kernel):
        R = point._curve._field
        k2 = kernel._x - kernel._z
        k3 = kernel._x + kernel._z
        k1 = kernel._z^2
        k1 = k1 + k1
        k1 = k1 + k1
        t0 = point._x + point._z
        t1 = point._x - point._z
        xx = t0 * k2
        zz = t1 * k3
        t0 = t0 * t1
        t0 = t0 * k1
        t1 = xx + zz
        zz = xx - zz
        t1 = t1^2
        zz = zz^2
        xx = t0 + t1
        t0 = zz - t0
        x = xx * t1
        z = zz * t0
        P = PointMCFp2(R(x), None, R(z), point._curve)
        return P.transformZ()
    
    
def coef_A(P,Q,PdiffQ):
    A = (1 - P._x * Q._x - P._x * PdiffQ._x - Q._x * PdiffQ._x)^2/(4 * P._x * Q._x * PdiffQ._x) - P._x - Q._x - PdiffQ._x
    return MontgomeryCurveFp2(P._curve._field, P._curve._field(A), 1)
    
