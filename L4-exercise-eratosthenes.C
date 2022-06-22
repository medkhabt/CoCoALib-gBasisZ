
#include "CoCoA/library.H"

using namespace std;

namespace CoCoA
{

  // Correct and improve this function.
  // Try with vector elem type long, int, short, char, bool;
  // discuss the trade-off between speed and memory required.
  // Reference: Wikipedia "Sieve of Eratosthenes"
    
    
        
    
    // on average with long it took 0.014321s 0.011446 0.002469 ( 0.000111 s for 10000) ( same as char for 64 )
    // on avg with int it took 0.008377s ( 7.2e-05s for 10000 ) (8e-06s for 64)
    
    // for short, it is not possible to calculate more than 16960. ( 4.8e-05 for 10000 ) ( same as char for 64 )
    
    // for char, it is not possible for more than 64, and even in case of 64 ( it took 5e-06s for 64 )
    
  std::vector<bool> MyEratosthenes(const long n)
  {
    vector<bool> sieve(n + 1,true);
    sieve[1] = false; // 1 is not prime
    for (long p=2; p <= n ; ++p)
    {
      if (!sieve[p]) continue;
      for (long j=2*p; j<=n; j+=p)
        sieve[j] = false;
    }
    return sieve;
  }

  void program()
  {
    GlobalManager CoCoAFoundations;

    const long n = 1000000;       //1000000;
    double t0 = CpuTime();
    auto S = MyEratosthenes(n);
    double t1 = CpuTime();
    cout << "Time: " << t1-t0 << endl;
    // How to check the result?
//      cout << "primary numbers are: " << endl;
//      for(int i = 2; i<=n; ++i) {
//          if(S[i]){
//              cout << i << ", ";
//          }
//      }
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
