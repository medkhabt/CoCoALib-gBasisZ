#include "CoCoA/library.H"

using namespace std;

namespace CoCoA
{

  // How to test this fn?  Check result for correctness?
  // How to improve this fn?  Speed test cases? [case of 1 for example it will give 1]
  // Documentation?

  // Compute GCD of a list of integers
  BigInt GcdList(vector<BigInt> L)
  {
    // Assume L is non-empty
    const long n = len(L);
    BigInt ans = L[0];
    for (int i=1; i < n; ++i)
    {
      CheckForInterrupt("GcdList");
      ans = gcd(ans, L[i]);
    }
    return ans;
  }


  void program()
  {
    GlobalManager CoCoAFoundations;
    SignalWatcher MonitorInterrupt(SIGINT); // you must also call CheckForInterrupt every so often

    vector<BigInt> L;
      
      for (int i = 0 ; i < 100000000; i++) {
          L.push_back(BigInt(1000200000 + i));
      }



    double t0 = CpuTime();
    BigInt N = GcdList(L);
    double t1 = CpuTime();
    cout << "gcd = " << N << "   time taken " << t1-t0 << endl;
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
