import invariant from 'tiny-invariant'
import { Currency } from './currency'
import { NativeCurrency } from './nativeCurrency'
import { Token } from './token'
import { WETH9 } from './weth9'

/**
 * Specify the symbol and name of specific chains
 * @param chainId Chain ID of the chain
 * @returns [Symbol, Name]
 */
function getSymbolAndName(chainId: number) {
  switch (chainId) {
    case 200810:
    case 200901:
      return ['BTC', 'BTC']
    case 46:
      return ['RING', 'RING']
    default:
      return ['ETH', 'Ether']
  }
}

/**
 * Ether is the main usage of a 'native' currency, i.e. for Ethereum mainnet and all testnets
 */
export class Ether extends NativeCurrency {
  protected constructor(chainId: number) {
    super(chainId, 18, getSymbolAndName(chainId)[0], getSymbolAndName(chainId)[1])
  }

  public get wrapped(): Token {
    const weth9 = WETH9[this.chainId]
    invariant(!!weth9, 'WRAPPED')
    return weth9
  }

  private static _etherCache: { [chainId: number]: Ether } = {}

  public static onChain(chainId: number): Ether {
    return this._etherCache[chainId] ?? (this._etherCache[chainId] = new Ether(chainId))
  }

  public equals(other: Currency): boolean {
    return other.isNative && other.chainId === this.chainId
  }
}
