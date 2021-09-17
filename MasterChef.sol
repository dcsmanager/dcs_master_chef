pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;


/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount)
        external
        returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender)
        external
        view
        returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    function burn(address _to, uint256 _amount) external;

    function mint(address _to, uint256 _amount) external;

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
}

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b)
        internal
        pure
        returns (bool, uint256)
    {
        uint256 c = a + b;
        if (c < a) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b)
        internal
        pure
        returns (bool, uint256)
    {
        if (b > a) return (false, 0);
        return (true, a - b);
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b)
        internal
        pure
        returns (bool, uint256)
    {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) return (true, 0);
        uint256 c = a * b;
        if (c / a != b) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b)
        internal
        pure
        returns (bool, uint256)
    {
        if (b == 0) return (false, 0);
        return (true, a / b);
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b)
        internal
        pure
        returns (bool, uint256)
    {
        if (b == 0) return (false, 0);
        return (true, a % b);
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) return 0;
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: division by zero");
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: modulo by zero");
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        return a - b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryDiv}.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a % b;
    }
}

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly {
            size := extcodesize(account)
        }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{value: amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return
            functionCallWithValue(
                target,
                data,
                value,
                "Address: low-level call with value failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value: value}(
            data
        );
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data)
        internal
        view
        returns (bytes memory)
    {
        return
            functionStaticCall(
                target,
                data,
                "Address: low-level static call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data)
        internal
        returns (bytes memory)
    {
        return
            functionDelegateCall(
                target,
                data,
                "Address: low-level delegate call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) private pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transfer.selector, to, value)
        );
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transferFrom.selector, from, to, value)
        );
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.approve.selector, spender, value)
        );
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(
            value
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(
            value,
            "SafeERC20: decreased allowance below zero"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(
            data,
            "SafeERC20: low-level call failed"
        );
        if (returndata.length > 0) {
            // Return data is optional
            // solhint-disable-next-line max-line-length
            require(
                abi.decode(returndata, (bool)),
                "SafeERC20: ERC20 operation did not succeed"
            );
        }
    }
}

// solhint-disable-next-line compiler-version
/**
 * @dev This is a base contract to aid in writing upgradeable contracts, or any kind of contract that will be deployed
 * behind a proxy. Since a proxied contract can't have a constructor, it's common to move constructor logic to an
 * external initializer function, usually called `initialize`. It then becomes necessary to protect this initializer
 * function so it can only be called once. The {initializer} modifier provided by this contract will have this effect.
 *
 * TIP: To avoid leaving the proxy in an uninitialized state, the initializer function should be called as early as
 * possible by providing the encoded function call as the `_data` argument to {UpgradeableProxy-constructor}.
 *
 * CAUTION: When used with inheritance, manual care must be taken to not invoke a parent initializer twice, or to ensure
 * that all initializers are idempotent. This is not verified automatically as constructors are by Solidity.
 */
abstract contract Initializable {
    /**
     * @dev Indicates that the contract has been initialized.
     */
    bool private _initialized;

    /**
     * @dev Indicates that the contract is in the process of being initialized.
     */
    bool private _initializing;

    /**
     * @dev Modifier to protect an initializer function from being invoked twice.
     */
    modifier initializer() {
        require(
            _initializing  || !_initialized,
            "Initializable: contract is already initialized"
        );

        bool isTopLevelCall = !_initializing;
        if (isTopLevelCall) {
            _initializing = true;
            _initialized = true;
        }

        _;

        if (isTopLevelCall) {
            _initializing = false;
        }
    }

   
}

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract ContextUpgradeable is Initializable {
    function __Context_init() internal initializer {
        __Context_init_unchained();
    }

    function __Context_init_unchained() internal initializer {}

    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }

    uint256[50] private __gap;
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract OwnableUpgradeable is Initializable, ContextUpgradeable {
    address private _owner;

    event OwnershipTransferred(
        address indexed previousOwner,
        address indexed newOwner
    );

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    function __Ownable_init() internal initializer {
        __Context_init_unchained();
        __Ownable_init_unchained();
    }

    function __Ownable_init_unchained() internal initializer {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(
            newOwner != address(0),
            "Ownable: new owner is the zero address"
        );
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }

    uint256[49] private __gap;
}

abstract contract ManagerUpgradeable is OwnableUpgradeable {
    //Administrator Address Mapping
    mapping(address => bool) public managers;

    function __Manager_init() internal initializer {
        OwnableUpgradeable.__Ownable_init();
        address ownerAddr = owner();
        setManager(ownerAddr);
    }

    //modifier
    modifier onlyManagers() {
        require(managers[msg.sender],"only Managers");
        _;
    }

    event SetManager(address indexed _manager);
    event RemoveManager(address indexed _manager);

    function setManager(address _manager) public onlyOwner {
        managers[_manager] = true;
        emit SetManager(_manager);
    }

    function removeManager(address _manager) public onlyOwner {
        delete managers[_manager];
        emit RemoveManager(_manager);
    }
}

/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
contract PausableUpgradeable is Initializable, ContextUpgradeable {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address indexed account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address indexed account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    function __Pausable_init() internal initializer {
        __Context_init_unchained();
        __Pausable_init_unchained();
    }

    function __Pausable_init_unchained() internal initializer {
        _paused = false;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view returns (bool) {
        return _paused;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        require(!_paused, "Pausable: paused");
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        require(_paused, "Pausable: not paused");
        _;
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }

    uint256[49] private __gap;
}

interface IAddressMap {
    function getMember(string memory name) external view returns (address addr);

    function getByets32(string memory source)
        external
        pure
        returns (bytes32 result);
}

interface ICash {
    function getInterval() external view returns (uint256);

    function withdrawChefFeeBonus(uint256 _interval) external;

    function pendingChefFeeBonus(uint256 _interval)
        external
        view
        returns (uint256[] memory);

    function tokenList() external view returns (address[] memory);

    function getTokenList() external view returns (address[] memory);
}

interface IIvite {
    function bind(address _superUser) external;

    function getUserInfo(address _user)
        external
        view
        returns (address, address[] memory);

    function getSuperUser(address _user) external view returns (address);
}

interface IVerify {
    function checkVerify(
        uint8 _g,
        bytes32 _s,
        string memory _t,
        address _f
    ) external view returns (bool);

    function checkBonusVerify(
        uint256[] memory _e,
        uint256 _start,
        uint256 _stop,
        address _f,
        string memory _t,
        bytes32 _s
    ) external view returns (bool);
}

// SPDX-License-Identifier: MIT

pragma solidity 0.6.12;

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow, so we distribute
        return (a / 2) + (b / 2) + (((a % 2) + (b % 2)) / 2);
    }
}

contract MasterChef is ManagerUpgradeable, PausableUpgradeable {
    using SafeERC20 for IERC20;
    using SafeMath for uint256;

    uint16 public PERCENTS_DIVIDER; //100**4 Digital frequency divider

    uint256 public burnAmount; //Number of tokens per burn
    uint256 public maxBurn; //Maximum amount of combustion
    uint256 public burnSum; //Number of tokens burned

    uint256 public maxMint; //Maximum value of minted token
    uint256 public mintAmount; //Number of tokens minted

    uint256 public periodsBlock; //Each block, the reward, needs to carry precision
    uint256 public startBlock; //Reward start block number
    uint256 public totalAllocPoint; //Allocate points and

    uint256 public staticMint; //The number of outputs counted
    uint256 public mintDebt; //The market has produced quantity

    //Information about the pool
    struct PoolInfo {
        uint256 allocPoint;
        uint256 lastRewardBlock;
        uint256 accTokenPerShare;
        uint256 totals;
    }
    PoolInfo[] public poolInfo;

    struct User {
        uint8 discard; //Upgrade is not allowed within the time limit of 1
        uint8 grade; //The grade at which the deposit is recorded
        uint256 totals; //Total cumulative investment
        uint256 lastBlock; //Last deposit block number
        uint256[7] rewardDebt; //User's incentive money
        uint256 lastRewardInterval; //The updated range of the final earnings
    }

    //Interval => Total pledges in the interval
    mapping(uint256 => uint256) public allIntervalTotals;
    // Interval => Token index => The amount of rewards available in the interval
    mapping(uint256 => mapping(uint256 => uint256)) public intervalBonus;
    // Interval => Token index => The amount of rewards issued in the interval
    // mapping(uint256 => mapping(uint256 => uint256)) public bonusDebt;

    uint256 public lastInterval; //Last update interval

    IAddressMap public addressMap;
    mapping(address => User) public users;
    uint256 public userTotalDeposit;

    // User => Interval => Pledge quantity
    mapping(address => mapping(uint256 => uint256)) public userIntervalTotals;
    uint256 public allDeposit; //The pledge amount
    // uint256 public forMax; //Cycle maximum
    // uint256 public forMaxInvite; //Loop sub maximum
    event Deposit(address indexed user, uint256 amount);
    event Withdraw(address indexed user, uint256 amount);
    event NewRegister(address indexed user, address parent);
    event EmergencyWithdraw(address indexed user, uint256 amount);
    event GenderDiscard(address indexed user);
    //Node combustion
    event BurnNodesReward(uint256 interval, uint256 amount);
    //Handling fee
    event UserWithdrawFeeBonus(
        address indexed user,
        uint256 interval,
        uint256 amount0,
        uint256 amount1,
        uint256 amount2,
        uint256 amount3
    );

    receive() external payable {}

    // The constructor
    function initialize(
        IAddressMap _addressMap,
        uint256 _tokenPerBlock,
        uint256 _startBlock
    ) public initializer {
        ManagerUpgradeable.__Manager_init();
        PausableUpgradeable.__Pausable_init();
        startBlock = _startBlock;
        periodsBlock = _tokenPerBlock;
        addressMap = _addressMap;
        lastInterval = 0;

        uint8[7] memory quto = [45, 10, 12, 10, 8, 8, 7];
        for (uint8 i = 0; i < quto.length; i++) {
            add(quto[i], false);
        }

        PERCENTS_DIVIDER = 1e4;
        burnAmount = 1e17;
        maxBurn = 21000000 * 1e18;
        maxMint = 24000000 * 1e18;
    }

    function poolLength() public view returns (uint256) {
        return poolInfo.length;
    }

    function add(uint256 allocPoint, bool withUpdate) public onlyOwner {
        if (withUpdate) {
            massUpdatePools();
        }
        uint256 lastRewardBlock = block.number > startBlock
            ? block.number
            : startBlock;
        totalAllocPoint = totalAllocPoint.add(allocPoint);
        poolInfo.push(
            PoolInfo({
                allocPoint: allocPoint,
                lastRewardBlock: lastRewardBlock,
                accTokenPerShare: 0,
                totals: 0
            })
        );
    }

    function set(
        uint256 pid,
        uint256 allocPoint,
        bool withUpdate
    ) public onlyOwner {
        if (withUpdate) {
            massUpdatePools();
        }
        totalAllocPoint = totalAllocPoint.sub(poolInfo[pid].allocPoint).add(
            allocPoint
        );
        poolInfo[pid].allocPoint = allocPoint;
    }

    function massUpdatePools() public {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            updatePool(pid, 0, 0);
        }
    }

    //Updated the reward variable, Mold 1 deposit increased, 2 withdrawal decreased
    function updatePool(
        uint256 pid,
        uint256 amount,
        uint8 mold
    ) internal {
        PoolInfo storage pool = poolInfo[pid];
        if (block.number <= pool.lastRewardBlock) {
            return;
        }
        uint256 supply = pool.totals;
        if (supply > 0) {
            uint256 multiplier = block.number.sub(pool.lastRewardBlock);
            uint256 tokenReward = multiplier
                .mul(periodsBlock)
                .mul(pool.allocPoint)
                .div(totalAllocPoint);

            //Casting the corresponding token
            if (tokenReward.add(mintAmount) <= maxMint) {
                IERC20(addressMap.getMember("token")).mint(
                    address(this),
                    tokenReward
                );
                staticMint += tokenReward;
                mintAmount += tokenReward;
            } else {
                IERC20(addressMap.getMember("token")).mint(
                    address(this),
                    maxMint.sub(mintAmount)
                );
                tokenReward = maxMint.sub(mintAmount);
                staticMint = maxMint;
                mintAmount = maxMint;
            }

            pool.accTokenPerShare = pool.accTokenPerShare.add(
                tokenReward.mul(1e12).div(supply)
            );
        }

        if (pid == 0) {
            if (mold == 1) {
                pool.totals = pool.totals.add(amount);
            } else if (mold == 2) {
                pool.totals = pool.totals.sub(Math.min(amount, pool.totals));
            }
        }

        pool.lastRewardBlock = block.number;
    }

    // The user account
    function deposit(
        uint256 amount,
        uint8 _g,
        bytes32 _s,
        string memory _t
    ) public whenNotPaused {
        address superUser = IIvite(addressMap.getMember("invite")).getSuperUser(
            msg.sender
        );
        require(superUser != address(0), "User is not activated");

        User storage user = users[msg.sender];
        uint8 grade = user.grade;
        uint8 newGrade = getGrade(msg.sender, amount, _g, _s, _t);
        require(newGrade >=0 && newGrade <=6,"newGrade out of range");
        
        updatePool(0, amount, 1);
        if (newGrade > 0) {
            updatePool(newGrade, amount, 1);
        }

        PoolInfo storage pool = poolInfo[0];
        if (user.totals > 0) {
            //Settlement proceeds
            uint256 pending = user
                .totals
                .mul(pool.accTokenPerShare)
                .div(1e12)
                .sub(user.rewardDebt[0]);

            if (grade > 0) {
                PoolInfo storage currentPoolNode = poolInfo[grade];
                pending = pending.add(
                    currentPoolNode.accTokenPerShare.div(1e12).sub(
                        user.rewardDebt[grade]
                    )
                );
            }
            safeERC20Transfer(msg.sender, pending);
            require(IERC20(addressMap.getMember("token")).balanceOf(address(this)) > userTotalDeposit,"contract balance lt userTotalDeposit");
        }
        IERC20(addressMap.getMember("token")).safeTransferFrom(
            address(msg.sender),
            address(this),
            amount
        );

        user.totals = user.totals.add(amount);
        allDeposit = allDeposit.add(amount);
        user.rewardDebt[0] = user.totals.mul(pool.accTokenPerShare).div(1e12);

        // If the user is an encrypted node
        // The number of nodes is updated
        // Update node level and node revenue
        if (grade != newGrade) {
            PoolInfo storage poolNode = poolInfo[grade];
            PoolInfo storage poolNewNode = poolInfo[newGrade];

            //demotion
            if (newGrade < grade) {
                if (newGrade == 0) {
                    poolNode.totals -= 1;
                } else {
                    poolNewNode.totals += 1;
                    poolNode.totals -= 1;
                }
            }

            //upgrade
            if (newGrade > grade) {
                if (grade == 0) {
                    poolNewNode.totals += 1;
                } else {
                    poolNewNode.totals += 1;
                    poolNode.totals -= 1;
                }
            }
            if (grade > 0) {
                user.rewardDebt[grade] = (poolNode.accTokenPerShare).div(1e12);
            }
            if (newGrade > 0) {
                user.rewardDebt[newGrade] = (poolNewNode.accTokenPerShare).div(
                    1e12
                );
            }
            user.grade = newGrade;

            if (poolNode.totals == 0) {
                poolNode.accTokenPerShare = 0;
                poolNode.lastRewardBlock = block.number;
            }
        } else {
            if (grade > 0) {
                PoolInfo storage poolNode = poolInfo[grade];
                user.rewardDebt[grade] = (poolNode.accTokenPerShare).div(1e12);
            }
        }

        // Update the pledge quantity within the interval
        // If the interval is inconsistent, the interval is updated and the processing fees available to the chef are migrated
        ICash cash = ICash(addressMap.getMember("cash"));
        uint256 interval = cash.getInterval();

        if (interval != lastInterval) {
            //Transfer interval commission
            migrateChefFee();
            //Burn interval tokens
            burnNodesReward();
        }

        userIntervalTotals[msg.sender][interval] += amount;
        allIntervalTotals[interval] = allIntervalTotals[interval].add(amount);
        userTotalDeposit.add(amount);
        emit Deposit(msg.sender, amount);
    }

    function migrateChefFee() public {
        ICash cash = ICash(addressMap.getMember("cash"));
        uint256 interval = cash.getInterval();
        if (interval != lastInterval) {
            // Interval update
            uint256 intervalDiffer = interval.sub(lastInterval);
            if (intervalDiffer != 0) {
                address[] memory tokenList = cash.getTokenList();
                for (uint256 i = 0; i < intervalDiffer; i++) {
                    uint256[] memory feeChefBonus = cash.pendingChefFeeBonus(
                        lastInterval + i
                    );
                    if (
                        feeChefBonus[0] != 0 ||
                        feeChefBonus[1] != 0 ||
                        feeChefBonus[2] != 0 ||
                        feeChefBonus[3] != 0
                    ) {
                        cash.withdrawChefFeeBonus(lastInterval + i);
                        for (uint256 j = 0; j < tokenList.length; j++) {
                            intervalBonus[lastInterval + i][j] = feeChefBonus[
                                j
                            ];
                        }
                    }
                }
            }
        }
    }

    /**
    @dev At the time the interval is updated, destroy additional tokens
     */
    function burnNodesReward() internal {
        ICash cash = ICash(addressMap.getMember("cash"));
        uint256 interval = cash.getInterval();

        uint256 intervalDiffer = interval.sub(lastInterval);
        if (intervalDiffer == 0) {
            return;
        }
        uint256 amount = 0;
        for (uint256 i = 0; i < intervalDiffer; i++) {
            for (uint256 j = 0; j < poolInfo.length; j++) {
                PoolInfo memory pool = poolInfo[j];
                if (pool.totals == 0 || pool.accTokenPerShare == 0) {
                    amount += periodsBlock.mul(7200).mul(pool.allocPoint).div(
                        totalAllocPoint
                    );
                }
            }
        }
        if (burnSum + amount > maxBurn) {
            amount = maxBurn - burnSum;
        }

        burnSum += amount;
        //The corresponding number of tokens is minted and burned
        IERC20(addressMap.getMember("token")).mint(address(this), amount);
        mintAmount += amount;
        staticMint += amount;

        IERC20(addressMap.getMember("token")).burn(address(this), amount);
        lastInterval = interval;
        emit BurnNodesReward(lastInterval, amount);
    }

    //Calculate user income, can receive income
    function pendingToken(address user) public view returns (uint256, uint256) {
        User storage currentUser = users[user];

        uint8 grade = currentUser.grade;

        PoolInfo storage pool = poolInfo[0];
        uint256 accTokenPerShare = pool.accTokenPerShare;
        if (block.number > pool.lastRewardBlock && pool.totals != 0) {
            //The product of reward
            uint256 multiplier = block.number.sub(pool.lastRewardBlock);
            uint256 tokenReward = multiplier
                .mul(periodsBlock)
                .mul(pool.allocPoint)
                .div(totalAllocPoint);

            accTokenPerShare = accTokenPerShare.add(
                tokenReward.mul(1e12).div(pool.totals)
            );
        }
        uint256 sum = currentUser.totals.mul(accTokenPerShare).div(1e12).sub(
            currentUser.rewardDebt[0]
        );

        uint256 gradeAmount = 0;
        if (grade > 0) {
            PoolInfo storage poolNode = poolInfo[grade];
            uint256 accTokenPerShareNode = poolNode.accTokenPerShare;
            if (
                block.number > poolNode.lastRewardBlock && poolNode.totals != 0
            ) {
                //The product of reward
                uint256 multiplierNode = block.number.sub(
                    poolNode.lastRewardBlock
                );
                uint256 tokenRewardNode = multiplierNode
                    .mul(periodsBlock)
                    .mul(poolNode.allocPoint)
                    .div(totalAllocPoint);
                accTokenPerShareNode = accTokenPerShareNode.add(
                    tokenRewardNode.mul(1e12).div(poolNode.totals)
                );

                gradeAmount = accTokenPerShareNode.div(1e12).sub(
                    currentUser.rewardDebt[grade]
                );
            }
        }

        return (sum, gradeAmount);
    }

    // When the user withdraws, when the withdrawal amount passes the critical value of 500 time, will permanently lose the level 1 qualification
    function withdraw(
        uint256 amount,
        uint8 _g,
        bytes32 _s,
        string memory _t
    ) public whenNotPaused {
        User storage user = users[msg.sender];
        require(user.totals >= amount, "withdraw:not good");

        uint8 grade = user.grade;
        updatePool(0, amount, 2);
        if (grade > 0) {
            updatePool(grade, 0, 2);
        }

        //Settlement proceeds
        PoolInfo storage pool = poolInfo[0];
        uint256 pending = user.totals.mul(pool.accTokenPerShare).div(1e12).sub(
            user.rewardDebt[0]
        );

        if (grade > 0) {
            PoolInfo storage poolNode = poolInfo[grade];
            pending = pending.add(
                poolNode.accTokenPerShare.div(1e12).sub(user.rewardDebt[grade])
            );
        }

        user.totals = user.totals.sub(amount);
        allDeposit = allDeposit.sub(amount);

        user.rewardDebt[0] = user.totals.mul(pool.accTokenPerShare).div(1e12);

        if (grade > 0) {
            PoolInfo storage poolNode = poolInfo[grade];
            user.rewardDebt[grade] = poolNode.accTokenPerShare.div(1e12);
        }

        uint256 sum = amount;
        if (amount >= burnAmount && burnSum < maxBurn) {
            IERC20(addressMap.getMember("token")).burn(
                address(this),
                burnAmount
            );
            sum = amount.sub(burnAmount);
            require(sum > 0,"real withdraw num need gt 0");
            burnSum += burnAmount;
        }
        safeERC20Transfer(msg.sender, pending);
        require(IERC20(addressMap.getMember("token")).balanceOf(address(this)) > userTotalDeposit,"contract balance lt userTotalDeposit");
        safeERC20Transfer(msg.sender, sum);
        emit Withdraw(msg.sender, amount);

        if (user.totals < 500 * 1e18 && grade > 0) {
            user.discard = 1;
            user.grade = 0;
            emit GenderDiscard(msg.sender);
        }

        uint8 newGrade = getGrade(msg.sender, 0, _g, _s, _t);
        if (grade != newGrade) {
            if (newGrade > 0) {
                updatePool(newGrade, 0, 2);
            }
            PoolInfo storage poolNode = poolInfo[grade];
            PoolInfo storage poolNewNode = poolInfo[newGrade];

            //demotion
            if (newGrade < grade) {
                if (newGrade == 0) {
                    poolNode.totals = 1;
                } else {
                    poolNewNode.totals = poolNewNode.totals.add(1);
                    poolNode.totals =poolNode.totals.sub(1);
                }
            }
            //upgrade
            if (newGrade > grade) {
                if (grade == 0) {
                    poolNewNode.totals = poolNewNode.totals.add(1);
                } else {
                    poolNewNode.totals =  poolNewNode.totals.add(1);
                    poolNode.totals = poolNode.totals.sub(1);
                }
            }
            if (grade > 0) {
                user.rewardDebt[grade] = (poolNode.accTokenPerShare).div(1e12);
            }

            if (newGrade > 0) {
                user.rewardDebt[newGrade] = (poolNewNode.accTokenPerShare).div(
                    1e12
                );
            }

            user.grade = newGrade;

            if (poolNode.totals == 0) {
                poolNode.accTokenPerShare = 0;
                poolNode.lastRewardBlock = block.number;
            }
        } else {
            if (grade > 0) {
                PoolInfo storage poolNode = poolInfo[grade];
                user.rewardDebt[grade] = (poolNode.accTokenPerShare).div(1e12);
            }
        }

        //If the intervals are not consistent, the interval updates are made and the processing fees available to the Chef are migrated
        ICash cash = ICash(addressMap.getMember("cash"));
        uint256 interval = cash.getInterval();

        if (interval != lastInterval) {
            //Transfer interval commission
            migrateChefFee();
            //Burn interval tokens
            burnNodesReward();
        }
        
         userTotalDeposit.sub(amount);
    }

    // Returns whether a user is an encrypted node
    function getIsEncryptionNode(address _user) public view returns (bool) {
        User memory user = users[_user];
        if (user.discard == 1) {
            return false;
        }
        if (user.totals >= 500 * 1e18) {
            return true;
        } else {
            return false;
        }
    }

    function getGrade(
        address _user,
        uint256 _amount,
        uint8 _g,
        bytes32 _s,
        string memory _t
    ) public view returns (uint8) {
        User memory currentUser = users[_user];
        if (currentUser.grade != 0 || currentUser.totals + _amount < 500 * 1e1) {
             if (!getIsEncryptionNode(_user)) {
                return 0;
            }
        } 
        
        require(
            IVerify(addressMap.getMember("verify")).checkVerify(
                _g,
                _s,
                _t,
                _user
            ),
            "Check failure"
        );
        if (currentUser.grade == 0) {
            if (
                currentUser.discard == 0 &&
                currentUser.totals.add(_amount) >= 500 * 1e18
            ) {
                return 1;
            }
        }
        return _g;
    }

    //Update the number of output blocks
    function updatePeriods(uint256 periods, bool withUpdate) public onlyOwner {
        if (withUpdate) {
            massUpdatePools();
        }
        periodsBlock = periods;
    }

    function safeERC20Transfer(address _to, uint256 _amount) internal {
        require(mintAmount <= maxMint, "The coins reached their maximum value");
        uint256 tokenBal = IERC20(addressMap.getMember("token")).balanceOf(
            address(this)
        );
        if (_amount > tokenBal) {
            if (mintAmount.add(_amount.sub(tokenBal)) > maxMint) {
                IERC20(addressMap.getMember("token")).mint(
                    address(this),
                    maxMint.sub(mintAmount)
                );
                staticMint += maxMint.sub(mintAmount);
                mintAmount += maxMint.sub(mintAmount);
            } else {
                staticMint += _amount.sub(tokenBal);
                mintAmount += _amount.sub(tokenBal);
                IERC20(addressMap.getMember("token")).mint(
                    address(this),
                    _amount.sub(tokenBal)
                );
            }
            tokenBal = IERC20(addressMap.getMember("token")).balanceOf(
                address(this)
            );
            IERC20(addressMap.getMember("token")).safeTransfer(_to, tokenBal);
        } else {
            IERC20(addressMap.getMember("token")).safeTransfer(_to, _amount);
        }
    }

    ///@dev Get output tokens available in the market
    function getMarketMintToken() public view returns (uint256) {
        return staticMint.mul(25).div(70).sub(mintDebt);
    }

    ///@dev Available output tokens for market withdrawals
    function marketWithdraw() public onlyManagers {
        uint256 pending = getMarketMintToken();
        if (pending > 0) {
            address gov1 = addressMap.getMember("gov1");
            address gov2 = addressMap.getMember("gov2");
            address gov3 = addressMap.getMember("gov3");
            require(
                gov1 != address(0) && gov2 != address(0) && gov3 != address(0),
                "Invalid Community address"
            );
            if (pending + mintAmount > maxMint) {
                pending = maxMint.sub(mintAmount);
            }
            IERC20(addressMap.getMember("token")).mint(
                gov1,
                pending.mul(40).div(100)
            );
            IERC20(addressMap.getMember("token")).mint(
                gov2,
                pending.mul(40).div(100)
            );
            IERC20(addressMap.getMember("token")).mint(
                gov3,
                pending.mul(20).div(100)
            );
            mintDebt = mintDebt.add(pending);
            mintAmount = mintAmount.add(pending);
        }
    }

    function getUserReward(address user, uint8 grade)
        public
        view
        returns (uint256)
    {
        User storage currentUser = users[user];
        return currentUser.rewardDebt[grade];
    }

    function getUserInfo(address user) public view returns (uint256, uint8) {
        User memory currentUser = users[user];
        return (currentUser.totals, currentUser.grade);
    }

    //Users receive commission dividends
    function withdrawFeeBonus(
        uint256[] memory _e,
        uint256 _start,
        uint256 _stop,
        string memory _t,
        bytes32 _s
    ) public {
        ICash cash = ICash(addressMap.getMember("cash"));
        uint256 interval = cash.getInterval();
        if (interval != lastInterval) {
            //Transfer interval commission
            migrateChefFee();
            //Burn interval tokens
            burnNodesReward();
        }
      
        
        User storage user = users[msg.sender];
        require(_start > user.lastRewardInterval, "The interval is the same");
        address[] memory tokenList = cash.getTokenList();
        require(
            IVerify(addressMap.getMember("verify")).checkBonusVerify(
                _e,
                _start,
                _stop,
                msg.sender,
                _t,
                _s
            ),
            "Check failure"
        );

        user.lastRewardInterval = _stop;
        
        //Proceeds are calculated, issued, and the final withdrawal interval is reset
        uint256[] memory feeBonus = _e;
        for (uint256 j = 0; j < tokenList.length; j++) {
            if (feeBonus[j] > 0) {
                if (address(tokenList[j]) == address(0)) {
                    Address.sendValue(msg.sender,feeBonus[j]);
                    // msg.sender.transfer(feeBonus[j]);
                } else {
                    IERC20(tokenList[j]).safeTransfer(msg.sender, feeBonus[j]);
                }
            }
        }
        require(IERC20(addressMap.getMember("token")).balanceOf(address(this)) >= userTotalDeposit,"contract balance lt or equals to userTotalDeposit");

       
        emit UserWithdrawFeeBonus(
            msg.sender,
            _stop,
            _e[0],
            _e[1],
            _e[2],
            _e[3]
        );
    }

    /**
    Aggregation function
    0、 Indicates the current block number
    1、 Number of combustion statistics
    2、 fluidity of mining pledge
    3、 Casting amount of liquid mining tokens
    4、 Interval token output
    Total amount of pledges
     */
    function argInfo()
        public
        view
        returns (
            uint256,
            uint256,
            uint256,
            uint256,
            uint256,
            uint256
        )
    {
        return (
            block.number,
            burnSum,
            IERC20(addressMap.getMember("token")).balanceOf(address(this)),
            mintAmount,
            periodsBlock.mul(7200),
            allDeposit
        );
    }

    // Assist in obtaining the user to invite the superior
    function getSuperUser(address _user) public view returns (address) {
        address superUser = IIvite(addressMap.getMember("invite")).getSuperUser(
            _user
        );
        return superUser;
    }

    //Obtaining the Token list
    function getTokenList() public view returns (address[] memory) {
        ICash cash = ICash(addressMap.getMember("cash"));
        return cash.getTokenList();
    }

    function getLastRewardInterval(address _addr)
        public
        view
        returns (uint256)
    {
        User memory user = users[_addr];
        return user.lastRewardInterval;
    }
    
     function emergencyWithdraw() public {
        User storage user = users[msg.sender];
        safeERC20Transfer(
            msg.sender,
            user.totals
        );
        userTotalDeposit.sub(user.totals);
        user.totals = 0;
        user.lastBlock = block.number;
        user.rewardDebt = [0, 0, 0, 0, 0, 0, 0];
        
        emit EmergencyWithdraw(msg.sender, user.totals);
    }
}
