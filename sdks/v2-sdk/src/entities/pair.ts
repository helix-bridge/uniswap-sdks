import { getCreate2Address } from '@ethersproject/address'
import { BigNumber } from '@ethersproject/bignumber'
import { keccak256, pack } from '@ethersproject/solidity'
import { BigintIsh, ChainId, CurrencyAmount, Percent, Price, sqrt, Token } from '@helix-bridge/sdk-core'
import JSBI from 'jsbi'
import invariant from 'tiny-invariant'

import {
  _1000,
  _997,
  BASIS_POINTS,
  FACTORY_ADDRESS,
  FACTORY_ADDRESS_MAP,
  FIVE,
  INIT_CODE_HASH,
  MINIMUM_LIQUIDITY,
  ONE,
  ONE_HUNDRED_PERCENT,
  ZERO,
  ZERO_PERCENT,
} from '../constants'
import { InsufficientInputAmountError, InsufficientReservesError } from '../errors'

function getPairAddress(token0: Token, token1: Token) {
  const { chainId } = token0
  switch (chainId) {
    case ChainId.BITLAYER_TESTNET:
      if (
        token0.address.toLowerCase() === '0x209ba92b5cc962673a30998ed7a223109d0be5e8'.toLowerCase() &&
        token1.address.toLowerCase() === '0xab40fe1dae842b209599269b8dafb0c54a743438'.toLowerCase()
      ) {
        // USDC / USDT
        return '0x3c15041d5ef66a32d8a89ea7f177cf15891d85f5'
      }
      if (
        token0.address.toLowerCase() === '0x209ba92b5cc962673a30998ed7a223109d0be5e8'.toLowerCase() &&
        token1.address.toLowerCase() === '0xf4340cf5f3891a3827713b33f769b501a0b5b122'.toLowerCase()
      ) {
        // USDC / BRC
        return '0x775953b64D4209b983928c177400b4d4EfD1D78e'
      }
      if (
        token0.address.toLowerCase() === '0x3e57d6946f893314324c975aa9cebbdf3232967e'.toLowerCase() &&
        token1.address.toLowerCase() === '0xf4340cf5f3891a3827713b33f769b501a0b5b122'.toLowerCase()
      ) {
        // WBTC / BRC
        return '0x3131f6DCE17AC1c351e5a3FA24A465F8d9f32655'
      }
      if (
        token0.address.toLowerCase() === '0x209ba92b5cc962673a30998ed7a223109d0be5e8'.toLowerCase() &&
        token1.address.toLowerCase() === '0x3e57d6946f893314324c975aa9cebbdf3232967e'.toLowerCase()
      ) {
        // USDC / WBTC
        return '0xA02E65f9C1E44d4f56b26c0F5f0414Bd204c9C80'
      }
      return null
    case ChainId.BITLAYER:
      if (
        token0.address.toLowerCase() === '0xfe9f969faf8ad72a83b761138bf25de87eff9dd2'.toLowerCase() &&
        token1.address.toLowerCase() === '0xff204e2681a6fa0e2c3fade68a1b28fb90e4fc5f'.toLowerCase()
      ) {
        // USDT / WBTC
        return '0x86aBD2Bcc2759B776747c0E3B6a41328B01e1384'
      }
      if (
        token0.address.toLowerCase() === '0x9827431e8b77e87c9894bd50b055d6be56be0030'.toLowerCase() &&
        token1.address.toLowerCase() === '0xfe9f969faf8ad72a83b761138bf25de87eff9dd2'.toLowerCase()
      ) {
        // USDC / USDT
        return '0xD184CB1441b94882bf2F35de356125E8AD5629A1'
      }
      return null
    case ChainId.DARWINIA:
      if (
        token0.address.toLowerCase() === '0x0000000000000000000000000000000000000403'.toLowerCase() &&
        token1.address.toLowerCase() === '0xE7578598Aac020abFB918f33A20faD5B71d670b4'.toLowerCase()
      ) {
        // ahUSDT / WRING
        return '0x89d1fa5c57dac3CB38d89e5e3bd33080D02d31b1'
      }
      return null
    default:
      return null
  }
}

export const computePairAddress = ({
  factoryAddress,
  tokenA,
  tokenB,
}: {
  factoryAddress: string
  tokenA: Token
  tokenB: Token
}): string => {
  const [token0, token1] = tokenA.sortsBefore(tokenB) ? [tokenA, tokenB] : [tokenB, tokenA] // does safety checks
  return getPairAddress(token0, token1) ?? getCreate2Address(
    factoryAddress,
    keccak256(['bytes'], [pack(['address', 'address'], [token0.address, token1.address])]),
    INIT_CODE_HASH
  )
}
export class Pair {
  public readonly liquidityToken: Token
  private readonly tokenAmounts: [CurrencyAmount<Token>, CurrencyAmount<Token>]

  public static getAddress(tokenA: Token, tokenB: Token): string {
    const factoryAddress = FACTORY_ADDRESS_MAP[tokenA.chainId] ?? FACTORY_ADDRESS
    return computePairAddress({ factoryAddress, tokenA, tokenB })
  }

  public constructor(currencyAmountA: CurrencyAmount<Token>, tokenAmountB: CurrencyAmount<Token>) {
    const tokenAmounts = currencyAmountA.currency.sortsBefore(tokenAmountB.currency) // does safety checks
      ? [currencyAmountA, tokenAmountB]
      : [tokenAmountB, currencyAmountA]
    this.liquidityToken = new Token(
      tokenAmounts[0].currency.chainId,
      Pair.getAddress(tokenAmounts[0].currency, tokenAmounts[1].currency),
      18,
      'UNI-V2',
      'Uniswap V2'
    )
    this.tokenAmounts = tokenAmounts as [CurrencyAmount<Token>, CurrencyAmount<Token>]
  }

  /**
   * Returns true if the token is either token0 or token1
   * @param token to check
   */
  public involvesToken(token: Token): boolean {
    return token.equals(this.token0) || token.equals(this.token1)
  }

  /**
   * Returns the current mid price of the pair in terms of token0, i.e. the ratio of reserve1 to reserve0
   */
  public get token0Price(): Price<Token, Token> {
    const result = this.tokenAmounts[1].divide(this.tokenAmounts[0])
    return new Price(this.token0, this.token1, result.denominator, result.numerator)
  }

  /**
   * Returns the current mid price of the pair in terms of token1, i.e. the ratio of reserve0 to reserve1
   */
  public get token1Price(): Price<Token, Token> {
    const result = this.tokenAmounts[0].divide(this.tokenAmounts[1])
    return new Price(this.token1, this.token0, result.denominator, result.numerator)
  }

  /**
   * Return the price of the given token in terms of the other token in the pair.
   * @param token token to return price of
   */
  public priceOf(token: Token): Price<Token, Token> {
    invariant(this.involvesToken(token), 'TOKEN')
    return token.equals(this.token0) ? this.token0Price : this.token1Price
  }

  /**
   * Returns the chain ID of the tokens in the pair.
   */
  public get chainId(): number {
    return this.token0.chainId
  }

  public get token0(): Token {
    return this.tokenAmounts[0].currency
  }

  public get token1(): Token {
    return this.tokenAmounts[1].currency
  }

  public get reserve0(): CurrencyAmount<Token> {
    return this.tokenAmounts[0]
  }

  public get reserve1(): CurrencyAmount<Token> {
    return this.tokenAmounts[1]
  }

  public reserveOf(token: Token): CurrencyAmount<Token> {
    invariant(this.involvesToken(token), 'TOKEN')
    return token.equals(this.token0) ? this.reserve0 : this.reserve1
  }

  /**
   * getAmountOut is the linear algebra of reserve ratio against amountIn:amountOut.
   * https://ethereum.stackexchange.com/questions/101629/what-is-math-for-uniswap-calculates-the-amountout-and-amountin-why-997-and-1000
   * has the math deduction for the reserve calculation without fee-on-transfer fees.
   *
   * With fee-on-transfer tax, intuitively it's just:
   * inputAmountWithFeeAndTax = 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn
   *                          = (1 - amountIn.sellFeesBips / 10000) * amountInWithFee
   * where amountInWithFee is the amountIn after taking out the LP fees
   * outputAmountWithTax = amountOut * (1 - amountOut.buyFeesBips / 10000)
   *
   * But we are illustrating the math deduction below to ensure that's the case.
   *
   * before swap A * B = K where A = reserveIn B = reserveOut
   *
   * after swap A' * B' = K where only k is a constant value
   *
   * getAmountOut
   *
   * A' = A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn # here 0.3% is deducted
   * B' = B - amountOut * (1 - amountOut.buyFeesBips / 10000)
   * amountOut = (B - B') / (1 - amountOut.buyFeesBips / 10000) # where A' * B' still is k
   *           = (B - K/(A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn))
   *             /
   *             (1 - amountOut.buyFeesBips / 10000)
   *           = (B - AB/(A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn))
   *             /
   *             (1 - amountOut.buyFeesBips / 10000)
   *           = ((BA + B * 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn - AB)/(A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn))
   *             /
   *             (1 - amountOut.buyFeesBips / 10000)
   *           = (B * 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn / (A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn)
   *             /
   *             (1 - amountOut.buyFeesBips / 10000)
   * amountOut * (1 - amountOut.buyFeesBips / 10000) = (B * 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn
   *                                                    /
   *                                                    (A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn)
   *
   * outputAmountWithTax = (B * 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn
   *                       /
   *                       (A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn)
   *                       = (B * 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn * 1000
   *                       /
   *                       ((A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn) * 1000)
   *                     = (B * (1 - amountIn.sellFeesBips / 10000) 997 * * amountIn
   *                       /
   *                       (1000 * A + (1 - amountIn.sellFeesBips / 10000) * 997 * amountIn)
   *                     = (B * (1 - amountIn.sellFeesBips / 10000) * inputAmountWithFee)
   *                       /
   *                       (1000 * A + (1 - amountIn.sellFeesBips / 10000) * inputAmountWithFee)
   *                     = (B * inputAmountWithFeeAndTax)
   *                       /
   *                       (1000 * A + inputAmountWithFeeAndTax)
   *
   * inputAmountWithFeeAndTax = (1 - amountIn.sellFeesBips / 10000) * inputAmountWithFee
   * outputAmountWithTax = amountOut * (1 - amountOut.buyFeesBips / 10000)
   *
   * @param inputAmount
   * @param calculateFotFees
   */
  public getOutputAmount(
    inputAmount: CurrencyAmount<Token>,
    calculateFotFees: boolean = true
  ): [CurrencyAmount<Token>, Pair] {
    invariant(this.involvesToken(inputAmount.currency), 'TOKEN')
    if (JSBI.equal(this.reserve0.quotient, ZERO) || JSBI.equal(this.reserve1.quotient, ZERO)) {
      throw new InsufficientReservesError()
    }
    const inputReserve = this.reserveOf(inputAmount.currency)
    const outputReserve = this.reserveOf(inputAmount.currency.equals(this.token0) ? this.token1 : this.token0)

    const percentAfterSellFees = calculateFotFees ? this.derivePercentAfterSellFees(inputAmount) : ZERO_PERCENT
    const inputAmountAfterTax = percentAfterSellFees.greaterThan(ZERO_PERCENT)
      ? CurrencyAmount.fromRawAmount(
          inputAmount.currency,
          percentAfterSellFees.multiply(inputAmount).quotient // fraction.quotient will round down by itself, which is desired
        )
      : inputAmount

    const inputAmountWithFeeAndAfterTax = JSBI.multiply(inputAmountAfterTax.quotient, _997)
    const numerator = JSBI.multiply(inputAmountWithFeeAndAfterTax, outputReserve.quotient)
    const denominator = JSBI.add(JSBI.multiply(inputReserve.quotient, _1000), inputAmountWithFeeAndAfterTax)
    const outputAmount = CurrencyAmount.fromRawAmount(
      inputAmount.currency.equals(this.token0) ? this.token1 : this.token0,
      JSBI.divide(numerator, denominator) // JSBI.divide will round down by itself, which is desired
    )

    if (JSBI.equal(outputAmount.quotient, ZERO)) {
      throw new InsufficientInputAmountError()
    }

    const percentAfterBuyFees = calculateFotFees ? this.derivePercentAfterBuyFees(outputAmount) : ZERO_PERCENT
    const outputAmountAfterTax = percentAfterBuyFees.greaterThan(ZERO_PERCENT)
      ? CurrencyAmount.fromRawAmount(
          outputAmount.currency,
          outputAmount.multiply(percentAfterBuyFees).quotient // fraction.quotient will round down by itself, which is desired
        )
      : outputAmount
    if (JSBI.equal(outputAmountAfterTax.quotient, ZERO)) {
      throw new InsufficientInputAmountError()
    }

    return [
      outputAmountAfterTax,
      new Pair(inputReserve.add(inputAmountAfterTax), outputReserve.subtract(outputAmountAfterTax)),
    ]
  }

  /**
   * getAmountIn is the linear algebra of reserve ratio against amountIn:amountOut.
   * https://ethereum.stackexchange.com/questions/101629/what-is-math-for-uniswap-calculates-the-amountout-and-amountin-why-997-and-1000
   * has the math deduction for the reserve calculation without fee-on-transfer fees.
   *
   * With fee-on-transfer fees, intuitively it's just:
   * outputAmountWithTax = amountOut / (1 - amountOut.buyFeesBips / 10000)
   * inputAmountWithTax = amountIn / (1 - amountIn.sellFeesBips / 10000) / 0.997
   *
   * But we are illustrating the math deduction below to ensure that's the case.
   *
   * before swap A * B = K where A = reserveIn B = reserveOut
   *
   * after swap A' * B' = K where only k is a constant value
   *
   * getAmountIn
   *
   * B' = B - amountOut * (1 - amountOut.buyFeesBips / 10000)
   * A' = A + 0.997 * (1 - amountIn.sellFeesBips / 10000) * amountIn # here 0.3% is deducted
   * amountIn = (A' - A) / (0.997 * (1 - amountIn.sellFeesBips / 10000))
   *          = (K / (B - amountOut / (1 - amountOut.buyFeesBips / 10000)) - A)
   *            /
   *            (0.997 * (1 - amountIn.sellFeesBips / 10000))
   *          = (AB / (B - amountOut / (1 - amountOut.buyFeesBips / 10000)) - A)
   *            /
   *            (0.997 * (1 - amountIn.sellFeesBips / 10000))
   *          = ((AB - AB + A * amountOut / (1 - amountOut.buyFeesBips / 10000)) / (B - amountOut / (1 - amountOut.buyFeesBips / 10000)))
   *            /
   *            (0.997 * (1 - amountIn.sellFeesBips / 10000))
   *          = ((A * amountOut / (1 - amountOut.buyFeesBips / 10000)) / (B - amountOut / (1 - amountOut.buyFeesBips / 10000)))
   *            /
   *            (0.997 * (1 - amountIn.sellFeesBips / 10000))
   *          = ((A * 1000 * amountOut / (1 - amountOut.buyFeesBips / 10000)) / (B - amountOut / (1 - amountOut.buyFeesBips / 10000)))
   *            /
   *            (997 * (1 - amountIn.sellFeesBips / 10000))
   *
   * outputAmountWithTax = amountOut / (1 - amountOut.buyFeesBips / 10000)
   * inputAmountWithTax = amountIn / (997 * (1 - amountIn.sellFeesBips / 10000))
   *                    = (A * outputAmountWithTax * 1000) / ((B - outputAmountWithTax) * 997)
   *
   * @param outputAmount
   */
  public getInputAmount(
    outputAmount: CurrencyAmount<Token>,
    calculateFotFees: boolean = true
  ): [CurrencyAmount<Token>, Pair] {
    invariant(this.involvesToken(outputAmount.currency), 'TOKEN')
    const percentAfterBuyFees = calculateFotFees ? this.derivePercentAfterBuyFees(outputAmount) : ZERO_PERCENT
    const outputAmountBeforeTax = percentAfterBuyFees.greaterThan(ZERO_PERCENT)
      ? CurrencyAmount.fromRawAmount(
          outputAmount.currency,
          JSBI.add(outputAmount.divide(percentAfterBuyFees).quotient, ONE) // add 1 for rounding up
        )
      : outputAmount

    if (
      JSBI.equal(this.reserve0.quotient, ZERO) ||
      JSBI.equal(this.reserve1.quotient, ZERO) ||
      JSBI.greaterThanOrEqual(outputAmount.quotient, this.reserveOf(outputAmount.currency).quotient) ||
      JSBI.greaterThanOrEqual(outputAmountBeforeTax.quotient, this.reserveOf(outputAmount.currency).quotient)
    ) {
      throw new InsufficientReservesError()
    }

    const outputReserve = this.reserveOf(outputAmount.currency)
    const inputReserve = this.reserveOf(outputAmount.currency.equals(this.token0) ? this.token1 : this.token0)

    const numerator = JSBI.multiply(JSBI.multiply(inputReserve.quotient, outputAmountBeforeTax.quotient), _1000)
    const denominator = JSBI.multiply(JSBI.subtract(outputReserve.quotient, outputAmountBeforeTax.quotient), _997)
    const inputAmount = CurrencyAmount.fromRawAmount(
      outputAmount.currency.equals(this.token0) ? this.token1 : this.token0,
      JSBI.add(JSBI.divide(numerator, denominator), ONE) // add 1 here is part of the formula, no rounding needed here, since there will not be decimal at this point
    )

    const percentAfterSellFees = calculateFotFees ? this.derivePercentAfterSellFees(inputAmount) : ZERO_PERCENT
    const inputAmountBeforeTax = percentAfterSellFees.greaterThan(ZERO_PERCENT)
      ? CurrencyAmount.fromRawAmount(
          inputAmount.currency,
          JSBI.add(inputAmount.divide(percentAfterSellFees).quotient, ONE) // add 1 for rounding up
        )
      : inputAmount
    return [inputAmountBeforeTax, new Pair(inputReserve.add(inputAmount), outputReserve.subtract(outputAmount))]
  }

  public getLiquidityMinted(
    totalSupply: CurrencyAmount<Token>,
    tokenAmountA: CurrencyAmount<Token>,
    tokenAmountB: CurrencyAmount<Token>
  ): CurrencyAmount<Token> {
    invariant(totalSupply.currency.equals(this.liquidityToken), 'LIQUIDITY')
    const tokenAmounts = tokenAmountA.currency.sortsBefore(tokenAmountB.currency) // does safety checks
      ? [tokenAmountA, tokenAmountB]
      : [tokenAmountB, tokenAmountA]
    invariant(tokenAmounts[0].currency.equals(this.token0) && tokenAmounts[1].currency.equals(this.token1), 'TOKEN')

    let liquidity: JSBI
    if (JSBI.equal(totalSupply.quotient, ZERO)) {
      liquidity = JSBI.subtract(
        sqrt(JSBI.multiply(tokenAmounts[0].quotient, tokenAmounts[1].quotient)),
        MINIMUM_LIQUIDITY
      )
    } else {
      const amount0 = JSBI.divide(JSBI.multiply(tokenAmounts[0].quotient, totalSupply.quotient), this.reserve0.quotient)
      const amount1 = JSBI.divide(JSBI.multiply(tokenAmounts[1].quotient, totalSupply.quotient), this.reserve1.quotient)
      liquidity = JSBI.lessThanOrEqual(amount0, amount1) ? amount0 : amount1
    }
    if (!JSBI.greaterThan(liquidity, ZERO)) {
      throw new InsufficientInputAmountError()
    }
    return CurrencyAmount.fromRawAmount(this.liquidityToken, liquidity)
  }

  public getLiquidityValue(
    token: Token,
    totalSupply: CurrencyAmount<Token>,
    liquidity: CurrencyAmount<Token>,
    feeOn: boolean = false,
    kLast?: BigintIsh
  ): CurrencyAmount<Token> {
    invariant(this.involvesToken(token), 'TOKEN')
    invariant(totalSupply.currency.equals(this.liquidityToken), 'TOTAL_SUPPLY')
    invariant(liquidity.currency.equals(this.liquidityToken), 'LIQUIDITY')
    invariant(JSBI.lessThanOrEqual(liquidity.quotient, totalSupply.quotient), 'LIQUIDITY')

    let totalSupplyAdjusted: CurrencyAmount<Token>
    if (!feeOn) {
      totalSupplyAdjusted = totalSupply
    } else {
      invariant(!!kLast, 'K_LAST')
      const kLastParsed = JSBI.BigInt(kLast)
      if (!JSBI.equal(kLastParsed, ZERO)) {
        const rootK = sqrt(JSBI.multiply(this.reserve0.quotient, this.reserve1.quotient))
        const rootKLast = sqrt(kLastParsed)
        if (JSBI.greaterThan(rootK, rootKLast)) {
          const numerator = JSBI.multiply(totalSupply.quotient, JSBI.subtract(rootK, rootKLast))
          const denominator = JSBI.add(JSBI.multiply(rootK, FIVE), rootKLast)
          const feeLiquidity = JSBI.divide(numerator, denominator)
          totalSupplyAdjusted = totalSupply.add(CurrencyAmount.fromRawAmount(this.liquidityToken, feeLiquidity))
        } else {
          totalSupplyAdjusted = totalSupply
        }
      } else {
        totalSupplyAdjusted = totalSupply
      }
    }

    return CurrencyAmount.fromRawAmount(
      token,
      JSBI.divide(JSBI.multiply(liquidity.quotient, this.reserveOf(token).quotient), totalSupplyAdjusted.quotient)
    )
  }

  private derivePercentAfterSellFees(inputAmount: CurrencyAmount<Token>): Percent {
    const sellFeeBips = this.token0.wrapped.equals(inputAmount.wrapped.currency)
      ? this.token0.wrapped.sellFeeBps
      : this.token1.wrapped.sellFeeBps
    if (sellFeeBips?.gt(BigNumber.from(0))) {
      return ONE_HUNDRED_PERCENT.subtract(new Percent(JSBI.BigInt(sellFeeBips)).divide(BASIS_POINTS))
    } else {
      return ZERO_PERCENT
    }
  }

  private derivePercentAfterBuyFees(outputAmount: CurrencyAmount<Token>): Percent {
    const buyFeeBps = this.token0.wrapped.equals(outputAmount.wrapped.currency)
      ? this.token0.wrapped.buyFeeBps
      : this.token1.wrapped.buyFeeBps
    if (buyFeeBps?.gt(BigNumber.from(0))) {
      return ONE_HUNDRED_PERCENT.subtract(new Percent(JSBI.BigInt(buyFeeBps)).divide(BASIS_POINTS))
    } else {
      return ZERO_PERCENT
    }
  }
}
