// Copyright (c) 2006  John Abbott,  Anna M. Bigatti
// This file is part of the CoCoALib suite of examples.
// You are free to use any part of this example in your own programs.

#include "CoCoA/library.H"
#include <chrono> // TODO: remove it afterward.
#include <thread> // TODO: remove it afterward.

using namespace std;

//----------------------------------------------------------------------
const string ShortDescription =
"Contains functions that compute strong Gröbner bases over the integers \n";
  

const string LongDescription =
  "Make a copy of this file (called \"foo.C\", say) and put your code \n"
  "inside the procedure \"program\".                                  \n"
  "To compile your file in the examples directory just do this:       \n"
  "  make foo                                                         \n";
//----------------------------------------------------------------------
// i need more examples for bigger polynomials, or for polynomials that will give a result of non one.

class NoElementFoundException: public exception {
    const string m_msg;
    public:
    NoElementFoundException(const string& msg): m_msg(msg) {
//        cout << "NoElementFoundException::NoElementFoundException - set m_msg to: " << m_msg << endl;
    }
    
    
};
namespace CoCoA
{
    
    //TODO:
    // better name, sugg: RemQuots.
    class Record {
        private: // data members;
            RingElem remainder;
            std::vector<RingElem> quotients;
        public :
            Record(ConstRefRingElem, const std::vector<RingElem>&);
            explicit Record(ConstRefRingElem);
            const RingElem& getRemainder() const{
                return this->remainder;
            }
            const std::vector<RingElem>& getQuotients() const{
                return this->quotients;
            }
        
        
    };
    // call a constructor to the other construcotr.
    // we explicitly allow an empty vector. maybe not do that in thefuture
    // we should check that all the elements in the vector should be in the same ring of r.
    Record::Record(ConstRefRingElem r, const std::vector<RingElem>& q) : remainder(r), quotients(q){}

    Record::Record(ConstRefRingElem r) :remainder(r){}

//  // no need to implement the isPid because it already exist in the ring file.
//    vector<RingElem> cleanListGENS(vector L) {
//
//
//    }
    
    
    // Implement NF
    // First we need to check if it a global monomial order or a local monomial order.
    // create existTopReduction function.
// create topReduction function.
    
// TODO change the implementation of this.
    ConstRefPPMonoidElem LM(ConstRefRingElem e){
        return LPP(e);
    }
    
    void getFactorAForTopReduction(BigInt& a, const BigInt& size) {
        
    }
    
    //TODO: implement also the check of lc(f) = a * lc(g) + b, with a <> 0 and b < lc(f) but how do we choose the a, we have some flexibilty
    // here but what is the optimal solution ?
    // for now i ll set b to be 0, but i will need to implement something that will start with setting value to b and trying to find the
    // first (a,b) solution of the equation, this is the naive solution for now.
    // existelementtopredu();
    void getElementTopReduction(RingElem& result, BigInt& aFactor,  ConstRefRingElem& h, const std::vector<RingElem>& generators){
//        cout << "Start of the getElementTopReduction functon" << endl;
//        cout << "LM(h) is : " << LM(h) << endl;
        for(auto &gen : generators) {
//            cout << "LM(gen) is : " << LM(gen) << endl;
//            cout << "isDivisible : " << IsDivisible(LM(h), LM(gen));
            BigInt LCofH = ConvertTo<BigInt>(LC(h));
            BigInt LCofGen = ConvertTo<BigInt>(LC(gen));
            if(IsDivisible(LM(h), LM(gen)) && !IsZero( LCofH / LCofGen ) ) {
                BigInt b = LCofH % LCofGen;
                if(b < LCofH) {
                    result = gen;
                    aFactor = LCofH / LCofGen;
                    return ;
                }
            }
        }
        throw(NoElementFoundException("Can't find any element that top reduces the given polynomial"));
    }
    
    //Doesn't check if g can top reduces h, there is the getElementTopReduction that use this, this should stay an inner function to the class/file.
    RingElem topReduction(const BigInt& aCoef,ConstRefRingElem h, ConstRefRingElem g) {
        // create a monomial which has the lmh/lmg and lc which is a and than multiply it by g and add it to h ;
        RingElem aAndLmQuotient = monomial(owner(h), aCoef, LM(h)/LM(g));
        return h - aAndLmQuotient * g;
    }
    //TODO : instead of the for loop to the find_if
    RingElem NF(RingElem f, const std::vector<RingElem>& generators) {
        RingElem h = f; // is this copy by ref or value ?
        
        // maybe it is better to copy the generators, so i can remove some of the generators that are not top reduction element, and
        // let filter the vector in every loop .
        try{
            while(!IsZero(h) /*&& !existElementTopReduction(h, generators)*/) {
              // instead of creating a new function that just test if there is an element that is a top reduction for h in gen. which do
              // the same thing as getElementTopReduction, we can throw an error in the function and catch it here to terminate the while loop.
            // Suggestion : check a if it is zero that means no elem was top reduced
                BigInt a;
                RingElem g;
                // return bool and check if it is true and break in case it is ..
                getElementTopReduction(g, a, h, generators);
//                cout << "NF: LC h before reduction: " << LC(h) << endl ;
                h = topReduction(a, h, g);
            }
        } catch(const NoElementFoundException e) {
//            cout << "finish the loop" << endl;
            return h;
        }
        
        // is there any case that i need this return ?
        return h;
    }
    
    
    bool isNecessaryGcdPair(ConstRefRingElem a, ConstRefRingElem b){
        return ( !(IsDivisible(LC(a), LC(b))) && !(IsDivisible(LC(b), LC(a))) );
    }
    
    RingElem sPolynomial(ConstRefRingElem a, ConstRefRingElem b){
            RingElem lmA = monomial(owner(a), LC(a), LPP(a));
            RingElem lmB = monomial(owner(b), LC(b), LPP(b));

            RingElem numerator =
                        lcm(lmA, lmB);
            return (numerator/lmA) * a - (numerator/lmB) * b;

        }
    
    RingElem sPolynomialNew(ConstRefRingElem a, ConstRefRingElem b){

        ConstRefPPMonoidElem lmA = LM(a);
        ConstRefPPMonoidElem lmB = LM(b);
        
        PPMonoidElem termLcm = lcm(lmA, lmB);
        
        
        BigInt lcaValue =  ConvertTo<BigInt>(LC(a));
        BigInt lcbValue = ConvertTo<BigInt>(LC(b));
        
        
        BigInt numerator = lcm(lcaValue, lcbValue);
        // af tf f - ag tg g //
        return monomial(owner(a), (numerator/lcbValue), (termLcm/lmA)) * a - monomial(owner(b), (numerator/lcaValue), (termLcm/lmB)) * b;

    }
    
    
    bool isGcdPolyUseless(ConstRefRingElem f,ConstRefRingElem g) {
        return (IsDivisible(LC(g), LC(f)));
    }
    
    bool isSPolyUseless(ConstRefRingElem f, ConstRefRingElem g){
        return (IsCoprime(LM(f), LM(g)) && IsCoprime(LC(f), LC(g)));
    }
    
    
    
//    bool isNecessarySPair(ConstRefRingElem a, ConstRefRingElem b) {
//        return ( gcd(
//                     monomial(owner(a), LC(a), LPP(a)),
//                     monomial(owner(b), LC(b), LPP(b))
//                     )
//                != 1);
//    }
//
    bool isNecessarySPair(ConstRefRingElem a, ConstRefRingElem b) {
        return ( !IsCoprime(LPP(a), LPP(b)) || !IsCoprime(LC(a), LC(b)) );
    }
    
    ConstRefPPMonoidElem LT(ConstRefRingElem a) {
//        RingElemAlias result = ;
        return LPP(a);
    }
    
    RingElem gcdPolynomial(ConstRefRingElem a, ConstRefRingElem b){
        ConstRefPPMonoidElem lta = LT(a);
        ConstRefPPMonoidElem ltb = LT(b);

        PPMonoidElem termLcm = lcm(lta, ltb);
        BigInt lcaValue =  ConvertTo<BigInt>(LC(a));
        BigInt lcbValue = ConvertTo<BigInt>(LC(b));

//        cout << "lcaValue " << lcaValue << ", lcbValue " << lcbValue << endl;
        GcdAndCofacs resultExt = ExtGcd(
                std::vector<BigInt>{lcaValue, lcbValue}); //GcdAndCofacs

//        cout << "cofacs are : " << resultExt.myCofacs.at(0) << ", " << resultExt.myCofacs.at(1) << endl;

//        if(IsOne(LPP(a))) {
//
//        }
//        else if(IsOne(LPP(b))) {
//
//        }
//        else {
//
//        }

//        RingElem result(owner(a), )
        //TODO:  in case one of the result have lpp equal to one.
        RingElem aPart = monomial(owner(a), resultExt.myCofacs.at(0), termLcm/lta);
//        cout << "aPart is one:" << IsOne(LPP(aPart)) << endl;
//        cout << "aPart lc " << LC(aPart) << " aPart LPP" << LPP(aPart) << endl;
        RingElem bPart = monomial(owner(b), resultExt.myCofacs.at(1), termLcm/ltb);
//        cout << "bPart is one:" << IsOne(bPart) << endl;
//        cout << "bPart lc " << LC(bPart) << " bPart LPP" << LPP(bPart) << endl;
//        cout << "the sum is zero" << IsZero(aPart + bPart) << endl;
        return (aPart * a + bPart * b); //
        //return ((D[1]*TermLcm)/LT(F))*F+((D[2]*TermLcm)/LT(G))*G
    }
    
    RingElem gcdPolynomialNew(ConstRefRingElem a, ConstRefRingElem b){
        // bf tf f + bg tg g // tf = t/ lmf tg = t/lmg // b = gcd lcf, lcg // gf
        ConstRefPPMonoidElem lma = LM(a);
        ConstRefPPMonoidElem lmb = LM(b);
        
        PPMonoidElem termLcm = lcm(lma, lmb);
        BigInt lcaValue =  ConvertTo<BigInt>(LC(a));
        BigInt lcbValue = ConvertTo<BigInt>(LC(b));
        
//        cout << "lcaValue " << lcaValue << ", lcbValue " << lcbValue << endl;
        GcdAndCofacs resultExt = ExtGcd(
                std::vector<BigInt>{lcaValue, lcbValue}); //GcdAndCofacs  this bf , bg ?
        
//        cout << "cofacs are : " << resultExt.myCofacs.at(0) << ", " << resultExt.myCofacs.at(1) << endl;
        
//        if(IsOne(LPP(a))) {
//
//        }
//        else if(IsOne(LPP(b))) {
//
//        }
//        else {
//
//        }
        
//        RingElem result(owner(a), )
        //TODO:  in case one of the result have lpp equal to one.
        RingElem aPart = monomial(owner(a), resultExt.myCofacs.at(0), termLcm/lma);
//        cout << "aPart is one:" << IsOne(LPP(aPart)) << endl;
//        cout << "aPart lc " << LC(aPart) << " aPart LPP" << LPP(aPart) << endl;
        RingElem bPart = monomial(owner(b), resultExt.myCofacs.at(1), termLcm/lmb);
//        cout << "bPart is one:" << IsOne(bPart) << endl;
//        cout << "bPart lc " << LC(bPart) << " bPart LPP" << LPP(bPart) << endl;
//        cout << "the sum is zero" << IsZero(aPart + bPart) << endl;
        return (aPart * a + bPart * b); //
        //return ((D[1]*TermLcm)/LT(F))*F+((D[2]*TermLcm)/LT(G))*G
    }
    
    
    //TODO: change the bool argument to a flag.
    //TODO: should ret a record instead of RingElem (maybe genetic in this case)
    //TODO: Big N and R in the name.
    // pass by ref poly.
    // raw pointer..
    // check if generators contains  zero poly.
    Record nRoverZZCORE(RingElem poly, const std::vector<RingElem>& generators, bool withQuotients){
        std::vector<RingElem> quotients(generators.size());
//        cout << "nRoverZZCore: first breakpoint" << endl;
        if(IsZero(poly)) {
            if(withQuotients){
                // get rid of new(s) so you can remove the
                return  Record(zero(owner(poly)), quotients);
            }
            else {
                return  Record(zero(owner(poly)));
            }
        }
//        cout << "nRoverZZCore: second breakpoint" << endl;
        RingElem reminderElem(owner(poly), poly);
        bool found = true;
        while (found) {
            found = false;
            unsigned long i = 1;
//            cout << "nRoverZZCore: third breakpoint" << endl;
            while (i < generators.size() && !found) {
//                cout << "nRoverZZCore: fourth breakpoint i: " << i  << endl;
                if(
                   IsDivisible( // OF LM , LM
                               // here i can check if the lc is divisible the other lc, and the same for the lpp
                               monomial(owner(poly), LC(reminderElem),LPP(reminderElem)),
                               monomial(owner(poly), LC(generators.at(i)),LPP(generators.at(i))))) {
//                                   cout << "nRoverZZCore: fifth breakpoint: " << endl;
                                   // TODO: called the quotionts.at() two times.
                                   ConstRefRingElem operation = monomial(owner(poly), LC(reminderElem)/ LC(generators.at(i)) ,LPP(reminderElem) / LPP(generators.at(i)));
                                   if(IsZero(quotients.at(i))) {
                                       quotients.at(i) = operation; // the ctr of elem creates a zero element of RingZZ()
                                   }
                                   else {
                                       quotients.at(i) = quotients.at(i) + operation;
                                   }
//                    quotients.at(i) +=  //
//                                   cout << "nRoverZZCore: six breakpoint: " << endl;
                    reminderElem = sPolynomial(reminderElem, generators.at(i));
//                                   cout << "nRoverZZCore: seven breakpoint: " << endl;
                    if(IsZero(reminderElem)) {
                        if(withQuotients) {
                            return  Record(zero(owner(poly)), quotients);
                        }
                        else {
                            return  Record(reminderElem); // (same as putting zero)
                        }
                    }
                    found = true; // i don't think this part of the code will get executed.
                }
                i++;
            }
        }
        
        
        if(withQuotients) {
            return  Record(reminderElem, quotients);
        }
        else {
            return  Record(reminderElem); // this repeats a lot of times , let's create a function for this functionality.
        }
    }
    
    // Buchberger's Algoa
    std::vector<RingElem> gBasisCoreV2( std::vector<RingElem>& generators) {
//        cout<< "gBasisCoreV2: inside gBasisCoreV2" << endl;
        const long length = generators.size();
         std::vector<RingElem> polynomials;
        
        // 2
        
//        cout << "gBasisCoreV2: starting the first loop "<< endl;
        // should i sort the polynomials list to prioritirize the gcds first before aplyaing spolynomial [Comment after theoreme 17]
        for (unsigned long i = 0; i < length - 1; i++) {
            for (unsigned long j = i + 1; j < length; j++) {
                // first we need to see if we can discard one.
                const RingElem fi = generators.at(i), fj = generators.at(j);
                
                if(!isGcdPolyUseless(fi, fj)) {
                        polynomials.push_back(gcdPolynomial(fi, fj));
                        cout << "we got a gcd poly : "  << endl;
                    
                    
                }
                if(!isSPolyUseless(fi, fj)) {
                        polynomials.push_back(sPolynomial(fi, fj));
                        cout << "we got a spoly: " <<endl;
                }
            }
        }
        
//        cout << "gBasisCoreV2: starting the while loop" << endl;
//        cout << "gBasisCoreV2: size of generators is  " << generators.size() << endl;
        // 3
            
        while(!polynomials.empty()) {
//            cout<<"polynomial size " << polynomials.size() << endl;
            // 4
            std::this_thread::sleep_for(std::chrono::seconds(5));
            cout << "************************" << endl;
            RingElem h = polynomials.back();
            polynomials.pop_back();  // p<- p \ {h}  TODO: check the list is not empty, behaviour unpredicted. or not because it will get checked
            // by the while condition,
            cout << "poly size is after pop back: "  << polynomials.size();
            // 5
            h = NF(h, generators);
            cout << "result of NF: " << h << endl ;
            // 6
            if(!IsZero(h)) {
                cout<< " inside the condition is not zero" << endl;
//                cout<< " polynom size before the new fill " << polynomials.size() <<endl;
                polynomials.clear();
//                cout << "polynom size after the clear" << polynomials.size() << endl ;
                for(auto &g : generators) {
                    if(!isGcdPolyUseless(h, g)) {
//                        cout << "is gdc poly not usless = " << gcdPolynomial(g, h) << endl;
                        polynomials.push_back(gcdPolynomial(g, h));

                    }
                    if(!isSPolyUseless(h, g)) {
//                        cout << "is spoly not useless = " << sPolynomial(g, h) << endl;
                        polynomials.push_back(sPolynomial(g, h));
                    }
                }
                

                generators.push_back(h);
//                std::sort(generators.begin(), generators.end(), [](auto gen1, auto gen2) {
//                    return abs(ConvertTo<BigInt>(LC(gen1))) > abs(ConvertTo<BigInt>(LC(gen2)));
//                });
                
                cout << "polyn size after being inside the condition after the fill in : " << polynomials.size() << endl;

                // check if the generators list is already having a strong standard represntation.

            }
            
//            std::this_thread::sleep_for(std::chrono::seconds(5));
        }
        cout << "gBasisCoreV2: end of the while loop" << endl;
    // do the loop
        // calculate NF
        // if we found a reduction (h is diff than 0) then
            // create a new list of p with spoly, gpoly of the new h and the element of the g.
            // and add h to the g elements .
        return generators;
    }
    std::vector<RingElem> gBasisCore(const std::vector<RingElem>& generators) {
        // size_t.
        long length = generators.size() ;
        std::vector<std::pair<unsigned long, unsigned long>> pairList;
        for (unsigned long i = 0; i < length - 1; i++) {
            for (unsigned long j = i + 1; j < length; j++) {
                pairList.push_back(std::make_pair(i,j));
//                cout << "the pair is : (" << i << "," << j << ")" << endl;
            }
        }
//        cout << "gBasisCore: first breakpoint " << endl;
        std::vector<RingElem> gb = generators;
        while (pairList.size() > 0) {
            std::pair<unsigned long, unsigned long> pair = pairList.front(); // is this a copy by ref. or value ?
            // for now i ll take the first element than remove it but there is also an other way
            // I can just reverse the list and start from the last element , i should test both of this cases.
            pairList.erase(pairList.begin());
            std::vector<RingElem> polynomials;
            
//            cout << "gBasisCore: second breakpoint " << endl;
            if(isNecessaryGcdPair(gb.at(std::get<0>(pair)), gb.at(std::get<1>(pair)))) {
                RingElem polynom = gcdPolynomial(gb.at(std::get<0>(pair)), gb.at(std::get<1>(pair))); //
                if(!IsZero(polynom) && IsOne(LPP(polynom))) {
                    //TODO: sPolynomial ? in case it is already done than gcdPolynomial() ?
                    
                }
//                cout << "------------------ polynom: " << polynom << endl;
                polynomials.push_back(polynom);
            }
//            cout << "gBasisCore: third breakpoint " << endl;
            if(isNecessarySPair(gb.at(std::get<0>(pair)), gb.at(std::get<1>(pair)))) {
                polynomials.push_back(sPolynomial(gb.at(std::get<0>(pair)), gb.at(std::get<1>(pair))));
            }
//            cout << "gBasisCore: fourth breakpoint " << endl;
            for(const RingElem& poly: polynomials) {
                RingElem remainder = nRoverZZCORE(poly, gb, false).getRemainder();
//                cout << "gBasisCore: fifth breakpoint " << endl;
                if(!IsZero(remainder)){
                    if(LC(remainder) < 0) {
                        remainder = -1 * remainder;
                    }
//                    cout << "gBasisCore: sixth breakpoint " << endl;
                    gb.push_back(remainder);
                    for(unsigned long i = 0; i < gb.size() - 1; i++) {
//                        cout << "gBasisCore: seventh breakpoint with i :" << i  << endl;
                        pairList.push_back(std::make_pair(i, gb.size() - 1));
                    }
                }
            }
            
//            cout << "gBasisCore: eight breakpoint" << endl;
    
            std::sort(
                      pairList.begin(),
                      pairList.end(),
                      [gb](std::pair<unsigned long, unsigned long> a, std::pair<unsigned long, unsigned long>b){
//                          cout << "gb size is : "  << gb.size() << endl;
//                          cout << "gBasisCore: nine breakpoint, a0: " << std::get<0>(a) << " ,a1: " << std::get<1>(a) <<
//                                "b0: " <<std::get<0>(b) << ", b1: " << std::get<1>(b) << endl;
                        
                          
                return (lcm(
                           LPP(gb.at(std::get<0>(a))), LPP(gb.at(std::get<1>(a))) )
                            < lcm(LPP(gb.at(std::get<0>(b))), LPP(gb.at(std::get<1>(b))))
                        );
            });
//            cout << "gBasisCore : last breakpoint in the while" << endl;
        }
        
//        cout << "gBasisCore : last breakpoint in the gBAsiscore" << endl;
        return gb;
        
    }
    
    //maybe use the same vector so we won't need to copy the list, and also we need to make sure that the list doesn't
    // get partially filled in case an exception happend.
    
    std::vector<RingElem> gBoverZZV2(std::vector<RingElem>& v) {
        if(v.empty()){
            throw std::invalid_argument("the list must not be null");
        }
        cout << "gBoverZZ: going to call gBasisCore(v)" << endl;
        return gBasisCoreV2(v);
    }
    std::vector<RingElem> gBoverZZ(const std::vector<RingElem>& v) {
        if(v.empty()){
            throw std::invalid_argument("the list must not be null");
        }
//        cout << "gBoverZZ: going to call gBasisCore(v)" << endl;
        return gBasisCore(v);
    }
    
    std::vector<RingElem> cleanListMZZ( std::vector<RingElem>& g){
        unsigned long length = g.size();
        if(length == 1) {
            return g;
        }
            std::sort(
                      g.begin(),
                      g.end(),
                      [g](RingElem a, RingElem b){
                          
                return (LT(a) < LT(b) or (LT(a) == LT(b) && abs(LC(a)) < abs(LC(b))));
            });
        
        std::vector<std::pair<unsigned long, unsigned long>> pairList;
        for (unsigned long i = 0; i < length - 1; i++) {
            for (unsigned long j = i + 1; j < length; j++) {
                pairList.push_back(std::make_pair(i,j));
//                cout << "the pair is : (" << i << "," << j << ")" << endl;
            }
        }
        
        for(std::pair<unsigned long, unsigned long> couple: pairList) {
            if(
               IsDivisible(LPP(g.at(std::get<0>(couple))), LPP(g.at(std::get<1>(couple)))) &&
               IsDivisible(LC(g.at(std::get<0>(couple))), LC(g.at(std::get<1>(couple))))
               ){
                   g.erase(g.begin() + std::get<1>(couple));
                   return cleanListMZZ(g);
            }
        }
        return g;
    }

    
    std::vector<RingElem> minimalGBoverZZ(const std::vector<RingElem>& v) {
        if(v.empty()) {
            throw std::invalid_argument("the list must not be null");
        }
        std::vector<RingElem> gb = gBasisCore(v);
        return cleanListMZZ(gb);
    }
    
    
  void program()
  {
    GlobalManager CoCoAFoundations;
    SignalWatcher MonitorInterrupt(SIGINT); // you must also call CheckForInterrupt every so often
      
      
    // first test of my file
      
      std::vector<RingElem> v;
      
      
      ring P = NewPolyRing(RingZZ(), symbols("x,y"));
      
      v.push_back(RingElem(P, "-x*y +y^2 +x +y"));
      v.push_back(RingElem(P, "-x^2 -x*y -y^2 -x-1"));
      v.push_back(RingElem(P, "-x^2 +x*y -y^2 +x +y"));
      
      //[-2*x^2 -x*y +y^2 +2*x +2*y,  -x^2 +x*y -2*x +y -1,  x^2 -2*x*y +2*y^2 +2*x +2*y]
      
//      v.push_back(RingElem(P, "-2*x^2 -x*y +y^2 +2*x + 2*y"));
//      v.push_back(RingElem(P, "-x^2 +x*y -2*x +y -1"));
//      v.push_back(RingElem(P, "x^2 -2*x*y +2*y^2 + 2*x + 2*y"));
      
      
      //[8*x^2 -5*x*y +5*y^2 +x -6*y -7,  9*x^2 -9*x*y +2*x -6*y +3,  6*x*y +y^2 +7*x +7*y +8]
        
//      v.push_back(RingElem(P, "8*x^2 -5*x*y +5*y^2 +x -6*y -7"));
//      v.push_back(RingElem(P, "9*x^2 -9*x*y +2*x -6*y +3"));
//      v.push_back(RingElem(P, "6*x*y +y^2 +7*x +7*y +8"));
      
//      cout << "finished creating the vector" << endl;

    
 
//      cout << gcdPolynomial(RingElem(P, "6 * x^2 + 1"), RingElem(P, "-4 * x^3 + 2")) << endl;
//      cout << sPolynomial(RingElem(P, "6 * x^2 + 1"), RingElem(P, "-4 * x^3 + 2")) << endl;
//
//      const clock_t begin_time = clock();
//      std:: vector<RingElem> result = gBoverZZ(v);
//      std::cout << "tine spent on gBoverZZ is: " <<  float( clock () - begin_time ) /  CLOCKS_PER_SEC;
//
//
//
//      cout << " the list after the basis thing: " << endl;
//      for(RingElem& ele: result) {
//          cout << ele << endl;
//      }
//
//
//
//
//      const clock_t begin_time1 = clock();
//      std:: vector<RingElem> resultminimum = minimalGBoverZZ(v);
//      std::cout << "tine spent on  minimal gBoverZZ is: " <<  float( clock () - begin_time1 ) /  CLOCKS_PER_SEC;
//
//      cout << " the list after the minimal gbasis thing: " << endl;
//      for(RingElem& ele: resultminimum) {
//          cout << ele << endl;
//      }

      std::vector<RingElem> gens ;
      gens.push_back(RingElem(P, "x^2 "));
      gens.push_back(RingElem(P, "x^4 + 7")); //"x^4 -9*x*y+2*x -6*y +3"
//      gens.push_back(RingElem(P, "x^2 +7*x +7*x^9 +8")); //6*x*y +y^2 +7*x +7*y +8


//      RingElem h = RingElem(P, "x^3");


//      cout << "Test the function getElementTopReduction" << endl ;
//      ConstRefRingElem getElementTopReduction(ConstRefRingElem h, const std::vector<ConstRefRingElem>& generators){
//      RingElem result10;
//      BigInt a;
//      getElementTopReduction(result10, a, h, gens);
//      cout<< "Result is : " << result10 << " and a is  " << a << endl;

//      cout << "the top reduction is : " << topReduction(a, h, result10) << endl;

//      cout << "the nf of h in the gens vector is " << NF(h, gens) << endl;


      cout << "new gBoverZZ : " << endl;

      const clock_t begin_time2 = clock();
      std:: vector<RingElem> result2 = gBoverZZV2(v);
      std::cout << "tine spent on gBoverZZ is: " <<  float( clock () - begin_time2 ) /  CLOCKS_PER_SEC << endl;

      std:: vector<RingElem> result3 = gBoverZZ(v);
          cout << " the list after the new implementation of gBoverZZV2  thing: " << endl;
          for(RingElem& ele: result2) {
              cout << ele << endl;
          }
      cout << " the list after the old implementation of gBoverzz" << endl;
      for(RingElem& ele: result3) {
          cout << ele << endl;
      }


      
      cout << ShortDescription << endl;
    cout << boolalpha; // so that bools print out as true/false

    

  }

} // end of namespace CoCoA

//----------------------------------------------------------------------
// Use main() to handle any uncaught exceptions and warn the user about them.
int main()
{
  try
  {
    CoCoA::program();
    return 0;
  }

  catch (const CoCoA::InterruptReceived& intr)
  {
    cerr << endl
         << "------------------------------" << endl
         << ">>>  CoCoALib interrupted  <<<" << endl
         << "------------------------------" << endl
         << "-->>  " << intr << "  <<--" << endl;
    return 2;
  }
  catch (const CoCoA::ErrorInfo& err)
  {
    cerr << "***ERROR***  UNCAUGHT CoCoA error";
    ANNOUNCE(cerr, err);
  }
  catch (const std::exception& exc)
  {
    cerr << "***ERROR***  UNCAUGHT std::exception: " << exc.what() << endl;
  }
  catch(...)
  {
    cerr << "***ERROR***  UNCAUGHT UNKNOWN EXCEPTION" << endl;
  }

  CoCoA::BuildInfo::PrintAll(cerr);
  return 1;
}



// run logs::


// 22.06.2022 (rough impl. )
//8*x^2 -5*x*y +5*y^2 +x -6*y -7
//9*x^2 -9*x*y +2*x -6*y +3
//6*x*y +y^2 +7*x +7*y +8
//27*x*y +45*y^2 -7*x -6*y -87

// gBoverZZ : result in 0.016046s , minimal gBoverzz: 0.0014669s but it varies by +/- 0.002

//8*x^2 -5*x*y +5*y^2 +x -6*y -7
//9*x^2 -9*x*y +2*x -6*y +3
//6*x*y +y^2 +7*x +7*y +8
//27*x*y +45*y^2 -7*x -6*y -87
//3
//77*x +75*y +246
//26*x -1
//2
//6473
//3235
//1079
//5
//359
//2587
//1



//----------------------------------------------------------------------
// RCS header/log in the next few lines
// $Header: /Volumes/Home_1/cocoa/cvs-repository/CoCoALib-0.99/examples/ex-empty.C,v 1.16 2021/12/14 08:35:43 abbott Exp $
// $Log: ex-empty.C,v $
// Revision 1.16  2021/12/14 08:35:43  abbott
// Summary: Uncommented code for printing out "interrupted" message
//
// Revision 1.15  2020/01/09 13:32:48  abbott
// Summary: Added comment
//
// Revision 1.14  2019/11/14 17:45:59  abbott
// Summary: Added SignalWatcher (in case you want to make your code interruptible)
//
// Revision 1.13  2017/12/01 21:30:10  abbott
// Summary: Added Anna to copyright
//
// Revision 1.12  2017/07/08 19:07:02  abbott
// Summary: Removed comment out (dodgy) code for reporting unhandled interrupts
//
// Revision 1.11  2016/11/18 18:05:15  abbott
// Summary: Added commented out code to catch InterruptReceived
//
// Revision 1.10  2015/06/29 14:23:19  abbott
// Summary: added missing CoCoA:: prefix
// Author: JAA
//
// Revision 1.9  2015/06/29 13:25:54  bigatti
// -- code in namespace CoCoA
//
// Revision 1.8  2015/06/25 14:19:02  abbott
// Summary: Added call to CoCoA::BuildInfo::Printall
// Author: JAA
//
// Revision 1.7  2013/05/28 07:07:04  bigatti
// -- added "cout << boolalpha": useful for testing
//
// Revision 1.6  2012/11/30 14:04:55  abbott
// Increased visibility of comment saying "put your code here".
//
// Revision 1.5  2010/12/17 16:07:54  abbott
// Ensured that all i/o in examples is on standard C++ streams
// (rather than GlobalInput(), etc).
//
// Revision 1.4  2008/10/07 12:12:54  abbott
// Removed useless commented out #include.
//
// Revision 1.3  2007/05/31 16:06:16  bigatti
// -- removed previous unwanted checked-in version
//
// Revision 1.1.1.1  2007/03/09 15:16:11  abbott
// Imported files
//
// Revision 1.9  2007/03/07 11:51:40  bigatti
// -- improved test alignment
//
// Revision 1.8  2007/03/03 14:15:45  bigatti
// -- "foundations" renamed into "GlobalManager"
//
// Revision 1.7  2007/03/02 17:46:40  bigatti
// -- unique RingZ and RingQ
// -- requires foundations.H ;  foundations blah;  (thik of a better name)
//
// Revision 1.6  2007/03/02 10:47:53  cocoa
// First stage of RingZ modifications -- tests do not compile currently, Anna will fix this.
//
// Revision 1.5  2007/03/01 13:52:59  bigatti
// -- minor: fixed typo
//
// Revision 1.4  2007/02/28 15:15:56  bigatti
// -- minor: removed quotes in description
//
// Revision 1.3  2007/02/12 16:27:43  bigatti
// -- added strings ShortDescription and LongDescription for indexing
//
// Revision 1.2  2007/02/10 18:44:03  cocoa
// Added "const" twice to each test and example.
// Eliminated dependency on io.H in several files.
// Improved BuildInfo, and added an example about how to use it.
// Some other minor cleaning.
//
// Revision 1.1.1.1  2006/05/30 11:39:36  cocoa
// Imported files
//
// Revision 1.1  2006/03/12 21:28:34  cocoa
// Major check in after many changes
//
